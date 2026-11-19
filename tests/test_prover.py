"""Unit and integration tests for symbolic simplifier and inductive prover."""

from __future__ import annotations

from sipl.parser import parse_program
from sipl.semantics.prover import (
    find_counterexamples,
    prove_program,
    synthesize_loop_hypothesis,
)
from sipl.semantics.symbolic import (
    SymConst,
    SymFact,
    SymMul,
    SymState,
    SymVar,
    eval_sym_bool,
    eval_sym_expr,
    parse_sym_bool,
    parse_sym_expr,
    simplify,
    subst,
    sym_equals,
)


def test_symbolic_constant_folding_and_identities() -> None:
    assert simplify(parse_sym_expr("2 + 3")) == SymConst(5)
    assert simplify(parse_sym_expr("0 * x")) == SymConst(0)
    assert simplify(parse_sym_expr("1 * x")) == SymVar("x")
    assert simplify(parse_sym_expr("x + 0")) == SymVar("x")
    assert simplify(parse_sym_expr("x - 0")) == SymVar("x")
    assert simplify(parse_sym_expr("x ** 0")) == SymConst(1)
    assert simplify(parse_sym_expr("x ** 1")) == SymVar("x")


def test_symbolic_linear_polynomial_normalization() -> None:
    e1 = simplify(parse_sym_expr("(y - k) - 1"))
    assert sym_equals(e1, parse_sym_expr("y - (k + 1)"))
    assert e1.format_unicode() == "y \u2212 (k + 1)"

    e2 = simplify(parse_sym_expr("(x - k*y) - y"))
    assert sym_equals(e2, parse_sym_expr("x - (k + 1)*y"))
    assert e2.format_unicode() == "x \u2212 (k + 1)y"

    e3 = simplify(parse_sym_expr("(x - y) + y"))
    assert e3 == SymVar("x")


def test_symbolic_power_products_and_factorials() -> None:
    p1 = simplify(parse_sym_expr("(x ** k) * x"))
    p2 = simplify(parse_sym_expr("x * (x ** k)"))
    expected_xk1 = parse_sym_expr("x ** (k + 1)")
    assert sym_equals(p1, expected_xk1)
    assert sym_equals(p2, expected_xk1)
    assert p1.format_unicode() == "x^(k + 1)"

    p3 = simplify(parse_sym_expr("(2 ** k) * 2"))
    assert sym_equals(p3, parse_sym_expr("2 ** (k + 1)"))
    assert p3.format_unicode() == "2^(k + 1)"

    f_step = subst(parse_sym_expr("f * (i + 1)"), {"f": SymFact(SymVar("k")), "i": SymVar("k")})
    assert simplify(f_step) == SymFact(parse_sym_expr("k + 1"))
    assert sym_equals(
        SymMul(SymFact(SymVar("k")), parse_sym_expr("k + 1")), parse_sym_expr("(k + 1)!")
    )


def test_symbolic_formatting_and_evaluation() -> None:
    xk = parse_sym_expr("x ** k")
    assert xk.format_unicode() == "x^k"
    assert xk.format_latex() == "{x}^{k}"

    xy = parse_sym_expr("x - k * y")
    assert xy.format_unicode() == "x \u2212 ky"

    st = SymState({"X": SymVar("x"), "Y": parse_sym_expr("y - k"), "R": xk})
    assert "X \u21a6 x" in st.format_unicode()
    assert r"\mapsto" in st.format_latex()

    expr = parse_sym_expr("(x div y) + (n!)")
    assert eval_sym_expr(expr, {"x": 7, "y": 4, "n": 4}) == 1 + 24

    pred = parse_sym_bool("x >= 1 and (y > 0 or not (z = 0))")
    assert eval_sym_bool(pred, {"x": 2, "y": 1, "z": 0}) is True
    assert eval_sym_bool(pred, {"x": 0, "y": 1, "z": 1}) is False


def test_prove_power_xy() -> None:
    src = """
    begin
      R := 1;
      while Y > 0 do
      begin
        R := R * X;
        Y := Y - 1
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="R == x**y",
        backward_invariants=["R * X**Y == r0 * x0**y0", "X == x0", "Y == y0 + k"],
        mode="hybrid",
    )
    assert report.status == "proved"
    assert report.hypothesis_source == "synthesized"
    assert report.base_case.status == "proved"
    assert report.inductive_step.status == "proved"
    assert report.termination_and_exit.status == "proved"
    assert "k* = y" in report.termination_and_exit.formula
    assert report.backward_induction is not None
    assert report.backward_induction.status == "proved"
    assert report.counterexamples == []
    assert "База індукції" in report.explanation_text
    assert "Крок індукції" in report.explanation_text
    assert report.to_dict()["status"] == "proved"


def test_prove_integer_division_x_div_y() -> None:
    src = """
    begin
      R := 0;
      while X >= Y do
      begin
        X := X - Y;
        R := R + 1
      end
    end
    """
    prog = parse_program(src).ast
    st_0, st_k, lims = synthesize_loop_hypothesis(prog, precondition="X > 0 and Y > 0")
    assert lims == []
    assert sym_equals(st_0["R"], SymConst(0))
    assert sym_equals(st_k["X"], parse_sym_expr("x - k * y"))
    assert sym_equals(st_k["R"], parse_sym_expr("k"))

    r1 = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="R == x div y",
        mode="hybrid",
    )
    assert r1.status == "proved"
    assert r1.base_case.status == "proved"
    assert r1.inductive_step.status == "proved"
    assert r1.termination_and_exit.status == "proved"
    assert r1.counterexamples == []

    r2 = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="X < y and R >= 0",
        mode="hybrid",
    )
    assert r2.status == "proved"
    assert r2.termination_and_exit.status == "proved"
    assert r2.counterexamples == []


def test_prove_subtraction_via_minus_one() -> None:
    src = """
    begin
      while Y > 0 do
      begin
        X := X - 1;
        Y := Y - 1
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="X == x - y",
        mode="hybrid",
    )
    assert report.status == "proved"
    assert report.base_case.status == "proved"
    assert report.inductive_step.status == "proved"
    assert report.termination_and_exit.status == "proved"
    assert report.counterexamples == []


def test_prove_arithmetic_progression_2_to_2n() -> None:
    src1 = """
    begin
      S := 0;
      I := 0;
      while N > 0 do
      begin
        I := I + 2;
        S := S + I;
        N := N - 1
      end
    end
    """
    prog1 = parse_program(src1).ast
    report1 = prove_program(
        prog1,
        precondition="N > 0",
        postcondition="S == n * (n + 1)",
        mode="forward_induction",
    )
    assert report1.status == "proved"
    assert report1.base_case.status == "proved"
    assert report1.inductive_step.status == "proved"
    assert report1.termination_and_exit.status == "proved"
    assert report1.counterexamples == []

    src2 = """
    begin
      S := 0;
      I := 1;
      while I <= N do
      begin
        S := S + 2 * I;
        I := I + 1
      end
    end
    """
    prog2 = parse_program(src2).ast
    report2 = prove_program(
        prog2,
        precondition="N > 0",
        postcondition="S == n * (n + 1)",
        mode="forward_induction",
    )
    assert report2.status == "proved"
    assert report2.counterexamples == []


def test_prove_three_to_the_x() -> None:
    src = """
    begin
      R := 1;
      while X > 0 do
      begin
        R := R * 3;
        X := X - 1
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="X > 0",
        postcondition="R == 3**x",
        mode="hybrid",
    )
    assert report.status == "proved"
    assert report.base_case.status == "proved"
    assert report.inductive_step.status == "proved"
    assert report.termination_and_exit.status == "proved"
    assert report.backward_induction is not None
    assert report.backward_induction.status == "proved"
    assert report.counterexamples == []


def test_prove_factorial_program() -> None:
    src = """
    begin
      R := 1;
      I := 0;
      while I < N do
      begin
        I := I + 1;
        R := R * I
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="N > 0",
        postcondition="R == n!",
        mode="forward_induction",
    )
    assert report.status == "proved"
    assert report.counterexamples == []


def test_user_supplied_correct_hypothesis_overrides_synthesis() -> None:
    src = """
    begin
      R := 1;
      while Y > 0 do
      begin
        R := R * X;
        Y := Y - 1
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="R == x**y",
        hypothesis={"X": "x", "Y": "y - k", "R": "x**k"},
        mode="forward_induction",
    )
    assert report.status == "proved"
    assert report.hypothesis_source == "user"
    assert report.base_case.status == "proved"
    assert report.inductive_step.status == "proved"
    assert report.termination_and_exit.status == "proved"


def test_wrong_hypothesis_disproved_with_counterexample() -> None:
    src = """
    begin
      R := 1;
      while Y > 0 do
      begin
        R := R * X;
        Y := Y - 1
      end
    end
    """
    prog = parse_program(src).ast
    report = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="R == x**y",
        hypothesis={"X": "x", "Y": "y - k", "R": "x * k"},
        mode="forward_induction",
    )
    assert report.status == "disproved"
    assert report.hypothesis_source == "user"
    assert report.base_case.status == "failed"
    assert report.inductive_step.status == "failed"
    assert len(report.counterexamples) > 0


def test_buggy_initialization_and_off_by_one_and_nontermination() -> None:
    buggy_init = parse_program(
        """
        begin
          R := 0;
          while Y > 0 do
          begin
            R := R * X;
            Y := Y - 1
          end
        end
        """
    ).ast
    r_init = prove_program(buggy_init, precondition="X > 0 and Y > 0", postcondition="R == x**y")
    assert r_init.status == "disproved"
    assert len(r_init.counterexamples) > 0

    buggy_guard = parse_program(
        """
        begin
          R := 1;
          while Y >= 0 do
          begin
            R := R * X;
            Y := Y - 1
          end
        end
        """
    ).ast
    r_guard = prove_program(buggy_guard, precondition="X > 0 and Y > 0", postcondition="R == x**y")
    assert r_guard.status == "disproved"
    assert len(r_guard.counterexamples) > 0

    non_term = parse_program(
        """
        begin
          R := 1;
          while Y > 0 do
          begin
            R := R * X;
            Y := Y + 1
          end
        end
        """
    ).ast
    cxs = find_counterexamples(non_term, precondition="X > 0 and Y > 0", max_steps=100)
    assert len(cxs) > 0
    r_non_term = prove_program(non_term, precondition="X > 0 and Y > 0", postcondition="R == x**y")
    assert r_non_term.status == "disproved"
    assert len(r_non_term.counterexamples) > 0


def test_buggy_postcondition_disproved() -> None:
    prog = parse_program(
        """
        begin
          R := 1;
          while Y > 0 do
          begin
            R := R * X;
            Y := Y - 1
          end
        end
        """
    ).ast
    report = prove_program(
        prog,
        precondition="X > 0 and Y > 0",
        postcondition="R == x + y",
        mode="hybrid",
    )
    assert report.status == "disproved"
    assert report.termination_and_exit.status == "counterexample"
    assert len(report.counterexamples) > 0


def test_nested_if_gcd_honest_partial_or_unsupported_with_limitations() -> None:
    gcd_prog = parse_program(
        """
        begin
          while A != B do
          begin
            if A > B then
              A := A - B
            else
              B := B - A
          end
        end
        """
    ).ast
    report = prove_program(
        gcd_prog,
        precondition="A > 0 and B > 0",
        invariant="A > 0 and B > 0",
        postcondition="A == B",
        mode="hybrid",
    )
    assert report.status in ("partial", "unsupported")
    assert report.status != "proved"
    assert len(report.limitations) > 0
    assert report.counterexamples == []

    bad_inv_report = prove_program(
        gcd_prog,
        precondition="A > 0 and B > 0",
        invariant="A == B",
        mode="hybrid",
    )
    assert bad_inv_report.status == "disproved"
    assert len(bad_inv_report.counterexamples) > 0
