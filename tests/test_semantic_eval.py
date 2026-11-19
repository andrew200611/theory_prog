"""Tests for the algebraic evaluator of A_SIPL semantic terms."""

from __future__ import annotations

import json

import pytest

from sipl import (
    Assign,
    If,
    SiplRuntimeError,
    State,
    parse_program,
    run_program,
)
from sipl.semantics import (
    ConstNumTerm,
    DerefTerm,
    EvalStep,
    EvaluationResult,
    SuperposAexpTerm,
    SuperposBoolTerm,
    SuperposCmpTerm,
    build_semantic_term,
    eval_tfa,
    eval_tfb,
    evaluate_semantic_term,
)

POWER_PROGRAM = """begin
    R := 1;
    while Y > 0 do
    begin
        R := R * X;
        Y := Y - 1
    end
end"""

DIV_PROGRAM = """begin
    R := 0;
    while X >= Y do
    begin
        X := X - Y;
        R := R + 1
    end
end"""

GCD_PROGRAM = """begin
    while ¬ M = N do
        if M > N then M := M - N else N := N - M
end"""


def test_workbook_power_x_y_evaluation() -> None:
    prog = parse_program(POWER_PROGRAM).ast
    term = build_semantic_term(prog).term
    st = State({"X": 5, "Y": 2})

    res = evaluate_semantic_term(term, st)
    assert isinstance(res, EvaluationResult)
    assert res.defined is True
    assert res.final_state == State({"X": 5, "Y": 0, "R": 25})
    assert res.undefined_reason is None
    assert res.error_code is None

    assert len(res.loop_iterations) == 2
    assert res.loop_iterations[0]["iteration"] == 1
    assert res.loop_iterations[0]["input_state"] == {"X": 5, "Y": 2, "R": 1}
    assert res.loop_iterations[0]["intermediate_states"] == [
        {"label": "st_0^1", "state": {"X": 5, "Y": 2, "R": 5}},
        {"label": "st_0^2", "state": {"X": 5, "Y": 1, "R": 5}},
    ]
    assert res.loop_iterations[0]["output_state"] == {"X": 5, "Y": 1, "R": 5}
    assert res.loop_iterations[1]["iteration"] == 2
    assert res.loop_iterations[1]["output_state"] == {"X": 5, "Y": 0, "R": 25}

    formulas = {step.formula_name for step in res.steps}
    assert {"AF_SEQ", "AF_AS", "AF_WH", "AF_S", "AF_DNM", "AF_CONST"} <= formulas
    assert "NumItWH" in res.explanation_text
    assert "st_0^1" in res.explanation_text
    assert "st_2" in res.explanation_text


def test_workbook_div_x_y_evaluation() -> None:
    prog = parse_program(DIV_PROGRAM).ast
    term = build_semantic_term(prog).term
    st = State({"X": 7, "Y": 4})

    res = evaluate_semantic_term(term, st)
    assert res.defined is True
    assert res.final_state == State({"X": 3, "Y": 4, "R": 1})
    assert len(res.loop_iterations) == 1
    assert res.loop_iterations[0]["output_state"] == {"X": 3, "Y": 4, "R": 1}
    assert "NumItWH" in res.explanation_text


def test_workbook_gcd_evaluation() -> None:
    prog = parse_program(GCD_PROGRAM).ast
    term = build_semantic_term(prog).term
    st = State({"M": 8, "N": 16})

    res = evaluate_semantic_term(term, st)
    assert res.defined is True
    assert res.final_state == State({"M": 8, "N": 8})
    assert len(res.loop_iterations) == 1
    formulas = {step.formula_name for step in res.steps}
    assert "AF_IF" in formulas
    assert "AF_WH" in formulas


@pytest.mark.parametrize(
    ("source", "init_map"),
    [
        (POWER_PROGRAM, {"X": 5, "Y": 2}),
        (POWER_PROGRAM, {"X": 3, "Y": 0}),
        (DIV_PROGRAM, {"X": 7, "Y": 4}),
        (DIV_PROGRAM, {"X": 2, "Y": 5}),
        (GCD_PROGRAM, {"M": 8, "N": 16}),
        (GCD_PROGRAM, {"M": 21, "N": 14}),
        ("begin skip end", {"X": 10}),
        (
            "begin if (X > 0) and (Y != 0) then R := (X div Y) + (X mod Y) else R := -1 end",
            {"X": 17, "Y": 5},
        ),
        (
            "begin if (X < 0) or (Y <= 0) then skip else X := X + 1 end",
            {"X": 2, "Y": 3},
        ),
        (
            "begin X := 1; while X < 1 do skip end",
            {},
        ),
    ],
)
def test_equivalence_with_ast_interpreter(source: str, init_map: dict[str, int]) -> None:
    prog = parse_program(source).ast
    st = State(init_map)
    interp_res = run_program(prog, st)
    term = build_semantic_term(prog).term
    sem_res = evaluate_semantic_term(term, st)

    assert sem_res.defined is interp_res.is_defined
    assert sem_res.final_state == interp_res.final_state


def test_eval_tfa_and_tfb_and_direct_evaluation() -> None:
    prog = parse_program("begin R := (X + 2) * (Y - 1) end").ast
    assert isinstance(prog.body, Assign)
    tfa = build_semantic_term(prog.body.expr).term
    assert isinstance(tfa, SuperposAexpTerm)

    st = State({"X": 3, "Y": 5})
    assert eval_tfa(tfa, st) == 20
    direct_a = evaluate_semantic_term(tfa, st)
    assert direct_a.defined is True
    assert direct_a.value == 20
    assert direct_a.final_state == st

    tfb = SuperposBoolTerm(
        op_name="and",
        args=[
            SuperposCmpTerm(op_name="gr", left=DerefTerm(var="X"), right=ConstNumTerm(value=0)),
            SuperposBoolTerm(
                op_name="neg",
                args=[
                    SuperposCmpTerm(
                        op_name="eq", left=DerefTerm(var="Y"), right=ConstNumTerm(value=0)
                    )
                ],
            ),
        ],
    )
    assert eval_tfb(tfb, st) is True
    direct_b = evaluate_semantic_term(tfb, st)
    assert direct_b.defined is True
    assert direct_b.value is True


def test_partial_functions_undefined_cases() -> None:
    undef_prog = parse_program("begin R := X + 1 end").ast
    undef_term = build_semantic_term(undef_prog).term
    res_undef = evaluate_semantic_term(undef_term, State({"Y": 5}))
    assert res_undef.defined is False
    assert res_undef.final_state is None
    assert res_undef.error_code == "E_UNDEFINED_VAR"
    assert "\u2191" in res_undef.explanation_text

    with pytest.raises(SiplRuntimeError) as exc_var:
        eval_tfa(DerefTerm(var="Missing"), State({}))
    assert exc_var.value.code == "E_UNDEFINED_VAR"

    div_zero_prog = parse_program("begin R := X div 0 end").ast
    div_zero_res = evaluate_semantic_term(
        build_semantic_term(div_zero_prog).term,
        State({"X": 10}),
    )
    assert div_zero_res.defined is False
    assert div_zero_res.final_state is None
    assert div_zero_res.error_code == "E_DIV_ZERO"

    mod_zero_prog = parse_program("begin R := X mod Y end").ast
    mod_zero_res = evaluate_semantic_term(
        build_semantic_term(mod_zero_prog).term,
        State({"X": 10, "Y": 0}),
    )
    assert mod_zero_res.defined is False
    assert mod_zero_res.final_state is None
    assert mod_zero_res.error_code == "E_MOD_ZERO"

    strict_or_prog = parse_program("begin if (1 = 1) or (Z = 0) then R := 1 else R := 2 end").ast
    strict_or_res = evaluate_semantic_term(build_semantic_term(strict_or_prog).term, State({}))
    assert strict_or_res.defined is False
    assert strict_or_res.error_code == "E_UNDEFINED_VAR"

    inf_prog = parse_program("begin while 1 = 1 do skip end").ast
    inf_res = evaluate_semantic_term(
        build_semantic_term(inf_prog).term,
        State({}),
        max_iterations=5,
    )
    assert inf_res.defined is False
    assert inf_res.final_state is None
    assert inf_res.error_code == "E_MAX_ITERATIONS"
    assert len(inf_res.loop_iterations) == 5

    step_res = evaluate_semantic_term(
        build_semantic_term(parse_program(POWER_PROGRAM).ast).term,
        State({"X": 2, "Y": 10}),
        max_steps=3,
    )
    assert step_res.defined is False
    assert step_res.error_code == "E_MAX_STEPS"


def test_theorem_1_2_monotonicity_and_equitonicity() -> None:
    gcd_term = build_semantic_term(parse_program(GCD_PROGRAM).ast).term
    st = State({"M": 8, "N": 16})
    st_ext = State({"M": 8, "N": 16, "L": 9})
    assert st.is_substate_of(st_ext)

    res = evaluate_semantic_term(gcd_term, st)
    res_ext = evaluate_semantic_term(gcd_term, st_ext)
    assert res.defined and res_ext.defined
    assert res.final_state == State({"M": 8, "N": 8})
    assert res_ext.final_state == State({"M": 8, "N": 8, "L": 9})
    assert res.final_state.is_substate_of(res_ext.final_state)

    for src, s1, s2 in [
        (POWER_PROGRAM, {"X": 5, "Y": 2}, {"X": 5, "Y": 2, "Z": 99}),
        (DIV_PROGRAM, {"X": 7, "Y": 4}, {"X": 7, "Y": 4, "K": -3}),
        (
            "begin if X > Y then Z := X - Y else Z := Y - X end",
            {"X": 3, "Y": 8},
            {"X": 3, "Y": 8, "W": 42},
        ),
    ]:
        t = build_semantic_term(parse_program(src).ast).term
        st1 = State(s1)
        st2 = State(s2)
        assert st1.is_substate_of(st2)
        r1 = evaluate_semantic_term(t, st1)
        r2 = evaluate_semantic_term(t, st2)
        assert r1.defined and r2.defined
        assert r1.final_state is not None and r2.final_state is not None
        assert r1.final_state.is_substate_of(r2.final_state)

    a_prog = parse_program("begin _ := X * 2 + Y end").ast
    assert isinstance(a_prog.body, Assign)
    a_term = build_semantic_term(a_prog.body.expr).term
    b_prog = parse_program("begin if (X > Y) or (Y = 0) then skip else skip end").ast
    assert isinstance(b_prog.body, If)
    b_term = build_semantic_term(b_prog.body.cond).term
    assert isinstance(a_term, SuperposAexpTerm)
    assert isinstance(b_term, SuperposBoolTerm)
    st_small = State({"X": 4, "Y": 3})
    st_big = State({"X": 4, "Y": 3, "EXTRA": 100})
    assert eval_tfa(a_term, st_small) == eval_tfa(a_term, st_big)
    assert eval_tfb(b_term, st_small) == eval_tfb(b_term, st_big)


def test_evaluation_result_json_serialization_and_validation() -> None:
    prog = parse_program(DIV_PROGRAM).ast
    term = build_semantic_term(prog).term
    res = evaluate_semantic_term(term, State({"X": 7, "Y": 4}))

    payload = res.to_dict()
    encoded = json.dumps(payload, ensure_ascii=False)
    decoded = json.loads(encoded)
    assert decoded["defined"] is True
    assert decoded["initial_state"] == {"X": 7, "Y": 4}
    assert decoded["final_state"] == {"X": 3, "Y": 4, "R": 1}
    assert len(decoded["steps"]) == len(res.steps)
    for step_obj in res.steps:
        assert isinstance(step_obj, EvalStep)

    with pytest.raises(ValueError):
        evaluate_semantic_term(term, State({}), max_iterations=-1)
    with pytest.raises(ValueError):
        evaluate_semantic_term(term, State({}), max_steps=-1)
