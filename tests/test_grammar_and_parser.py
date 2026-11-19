"""Tests for SIPL formal grammar, lexer, parser, AST/ParseTree, State, and interpreter."""

from __future__ import annotations

import pytest

from sipl import (
    Assign,
    BinaryAexp,
    BinaryBexp,
    Block,
    CompareBexp,
    If,
    NotBexp,
    Number,
    ParenAexp,
    ParenBexp,
    Program,
    Seq,
    SiplRuntimeError,
    SiplSyntaxError,
    SipSyntaxError,
    Skip,
    State,
    StateParseError,
    Variable,
    While,
    __version__,
    eval_aexp,
    eval_bexp,
    parse_program,
    run_program,
)

POWER_PROGRAM = """begin
    R := 1;
    while Y > 0 do
    begin
        R := R * X;
        Y := Y - 1
    end
end"""

GCD_PROGRAM = """begin
    while ¬ M = N do
        if M > N then M := M – N else N := N – M
end"""


def test_version_and_aliases() -> None:
    assert __version__ == "1.0.0"
    assert SipSyntaxError is SiplSyntaxError


def test_golden_power_program_24_leaf_numbered_crown() -> None:
    res = parse_program(POWER_PROGRAM)
    assert res.is_crown_valid is True
    expected_crown = (
        "1 begin 2 R 3 := 4 1 5 ; 6 while 7 Y 8 > 9 0 10 do 11 begin "
        "12 R 13 := 14 R 15 * 16 X 17 ; 18 Y 19 := 20 Y 21 - 22 1 23 end 24 end"
    )
    assert res.parse_tree.numbered_crown() == expected_crown
    assert len(res.parse_tree.leaves()) == 24
    assert len(res.tokens) == 24


def test_golden_power_program_parse_tree_structure_fig1() -> None:
    res = parse_program(POWER_PROGRAM)
    pt = res.parse_tree
    assert pt.label == "<програма>"
    assert pt.category == "Prog"
    assert pt.rule_name == "NP1"
    assert pt.ast_node_id == res.ast.node_id

    seq_pt = pt.children[1]
    assert seq_pt.label == "<оператор>"
    assert seq_pt.rule_name == "NS2"

    init_pt = seq_pt.children[0]
    assert init_pt.rule_name == "NS1"
    assert init_pt.children[0].label == "<змінна>"
    assert init_pt.children[0].rule_name == "NV"
    assert init_pt.children[2].label == "<вираз>"
    assert init_pt.children[2].rule_name == "NA1"
    assert init_pt.children[2].children[0].label == "<число>"
    assert init_pt.children[2].children[0].rule_name == "NN"

    while_pt = seq_pt.children[2]
    assert while_pt.rule_name == "NS4"
    cond_pt = while_pt.children[1]
    assert cond_pt.label == "<умова>"
    assert cond_pt.rule_name == "NB2"
    block_pt = while_pt.children[3]
    assert block_pt.rule_name == "NS5"
    body_seq_pt = block_pt.children[1]
    assert body_seq_pt.rule_name == "NS2"
    mul_assign_pt = body_seq_pt.children[0]
    mul_expr_pt = mul_assign_pt.children[2]
    assert mul_expr_pt.rule_name == "NA5"
    assert mul_expr_pt.children[0].rule_name == "NA2"
    assert mul_expr_pt.children[0].children[0].rule_name == "NV"
    assert mul_expr_pt.children[2].rule_name == "NA2"


def test_all_core_sipl_constructs_strict_bnf() -> None:
    src = """begin
        skip;
        X := -1 + (2 * 3 - 4);
        if (X = 5) ∨ ¬(X > 10) then
            begin
                Y := X
            end
        else
            skip
    end"""
    res = parse_program(src, strict_bnf=True)
    assert res.is_crown_valid
    assert isinstance(res.ast, Program)
    assert isinstance(res.ast.body, Seq)
    assert isinstance(res.ast.body.left, Seq)
    assert isinstance(res.ast.body.left.left, Skip)
    assign = res.ast.body.left.right
    assert isinstance(assign, Assign)
    assert isinstance(assign.expr, BinaryAexp)
    assert isinstance(assign.expr.left, Number)
    assert assign.expr.left.value == -1
    assert isinstance(assign.expr.right, ParenAexp)
    if_stm = res.ast.body.right
    assert isinstance(if_stm, If)
    assert isinstance(if_stm.cond, BinaryBexp)
    assert if_stm.cond.op == "or"
    assert isinstance(if_stm.cond.left, ParenBexp)
    assert isinstance(if_stm.cond.right, NotBexp)
    assert isinstance(if_stm.then_branch, Block)
    assert isinstance(if_stm.else_branch, Skip)


def test_gcd_program_precedence_not_lower_than_comparison() -> None:
    res = parse_program(GCD_PROGRAM, strict_bnf=True)
    assert res.is_crown_valid
    while_stm = res.ast.body
    assert isinstance(while_stm, While)
    assert isinstance(while_stm.cond, NotBexp)
    assert isinstance(while_stm.cond.operand, CompareBexp)
    assert while_stm.cond.operand.op == "="
    assert isinstance(while_stm.cond.operand.left, Variable)
    assert while_stm.cond.operand.left.name == "M"
    assert isinstance(while_stm.cond.operand.right, Variable)
    assert while_stm.cond.operand.right.name == "N"


def test_left_associative_subtraction() -> None:
    res = parse_program("begin R := A - B - C end", strict_bnf=True)
    assign = res.ast.body
    assert isinstance(assign, Assign)
    assert isinstance(assign.expr, BinaryAexp)
    assert assign.expr.op == "-"
    assert isinstance(assign.expr.left, BinaryAexp)
    assert assign.expr.left.op == "-"
    assert isinstance(assign.expr.left.left, Variable)
    assert assign.expr.left.left.name == "A"
    assert isinstance(assign.expr.left.right, Variable)
    assert assign.expr.left.right.name == "B"
    assert isinstance(assign.expr.right, Variable)
    assert assign.expr.right.name == "C"


def test_arithmetic_precedence_mul_over_add() -> None:
    res = parse_program("begin R := X + Y * Z end", strict_bnf=True)
    assign = res.ast.body
    assert isinstance(assign, Assign)
    assert isinstance(assign.expr, BinaryAexp)
    assert assign.expr.op == "+"
    assert isinstance(assign.expr.right, BinaryAexp)
    assert assign.expr.right.op == "*"


def test_while_precedence_higher_than_semicolon() -> None:
    res = parse_program("begin while X > 0 do X := X - 1 ; R := 42 end", strict_bnf=True)
    assert isinstance(res.ast.body, Seq)
    assert isinstance(res.ast.body.left, While)
    assert isinstance(res.ast.body.left.body, Assign)
    assert res.ast.body.left.body.var == "X"
    assert isinstance(res.ast.body.right, Assign)
    assert res.ast.body.right.var == "R"


def test_if_precedence_higher_than_semicolon() -> None:
    res = parse_program(
        "begin if X > 0 then R := 1 else R := 2 ; Y := 3 end",
        strict_bnf=True,
    )
    assert isinstance(res.ast.body, Seq)
    assert isinstance(res.ast.body.left, If)
    assert isinstance(res.ast.body.left.else_branch, Assign)
    assert res.ast.body.left.else_branch.var == "R"
    assert isinstance(res.ast.body.right, Assign)
    assert res.ast.body.right.var == "Y"


def test_bexp_precedence_or_and_not_comparison() -> None:
    res = parse_program("begin if ¬ A = 1 and B > 2 or C < 3 then skip else skip end")
    if_stm = res.ast.body
    assert isinstance(if_stm, If)
    assert isinstance(if_stm.cond, BinaryBexp)
    assert if_stm.cond.op == "or"
    assert isinstance(if_stm.cond.left, BinaryBexp)
    assert if_stm.cond.left.op == "and"
    assert isinstance(if_stm.cond.left.left, NotBexp)
    assert isinstance(if_stm.cond.left.left.operand, CompareBexp)


def test_paren_aexp_inside_bexp_disambiguation() -> None:
    res = parse_program("begin if (X + 1) * 2 > (Y - 3) then skip else skip end")
    if_stm = res.ast.body
    assert isinstance(if_stm, If)
    assert isinstance(if_stm.cond, CompareBexp)
    assert if_stm.cond.op == ">"
    assert isinstance(if_stm.cond.left, BinaryAexp)
    assert isinstance(if_stm.cond.left.left, ParenAexp)
    assert isinstance(if_stm.cond.right, ParenAexp)


def test_negative_numbers_in_unary_positions_vs_subtraction() -> None:
    res = parse_program(
        "begin A := -5; B := (-10) + -2; C := A - 1; D := A - -3; E := - 7 end"
    )
    assert res.is_crown_valid
    stm = res.ast.body
    assigns: list[Assign] = []
    while isinstance(stm, Seq):
        assert isinstance(stm.right, Assign)
        assigns.append(stm.right)
        stm = stm.left
    assert isinstance(stm, Assign)
    assigns.append(stm)
    assigns.reverse()
    assert [a.var for a in assigns] == ["A", "B", "C", "D", "E"]
    assert isinstance(assigns[0].expr, Number) and assigns[0].expr.value == -5
    assert isinstance(assigns[2].expr, BinaryAexp) and assigns[2].expr.op == "-"
    assert isinstance(assigns[3].expr, BinaryAexp)
    assert isinstance(assigns[3].expr.right, Number) and assigns[3].expr.right.value == -3
    assert isinstance(assigns[4].expr, Number) and assigns[4].expr.value == -7


def test_extended_operators_and_unicode_aliases() -> None:
    src = """begin
        X := 17 div 3 + 17 mod 3;
        if X ≥ 7 ∧ Y ≤ 10 ∧ X ≠ 0 then
            if Y < 5 or ¬(X >= 10) then skip else skip
        else
            if X <> 1 and X <= 20 then skip else skip
    end"""
    res = parse_program(src, strict_bnf=False)
    assert res.is_crown_valid
    data = res.to_dict()
    assert data["ast"]["kind"] == "Program"
    assert data["parse_tree"]["rule_name"] == "NP1"


def test_comments_and_symbol_font_glyphs() -> None:
    src = """(* header comment *)
    begin
        // line comment
        # hash comment
        while \uf0d8 M = N do
            if M > N \uf0da N > M then skip else skip
    end"""
    res = parse_program(src, strict_bnf=True)
    assert res.is_crown_valid
    assert isinstance(res.ast.body, While)
    assert isinstance(res.ast.body.cond, NotBexp)


def test_ast_source_spans_accurate_line_and_column() -> None:
    src = "begin\n  R := 1;\n  Y := Y - 1\nend"
    res = parse_program(src)
    assert res.ast.span.start.line == 1
    assert res.ast.span.start.column == 1
    assert res.ast.span.end.line == 4
    assert res.ast.span.end.column == 4

    assert isinstance(res.ast.body, Seq)
    first_assign = res.ast.body.left
    second_assign = res.ast.body.right
    assert first_assign.span.start.line == 2
    assert first_assign.span.start.column == 3
    assert first_assign.span.end.line == 2
    assert first_assign.span.end.column == 9

    assert second_assign.span.start.line == 3
    assert second_assign.span.start.column == 3
    assert second_assign.span.end.line == 3
    assert second_assign.span.end.column == 13


def test_double_negation_and_nested_blocks() -> None:
    res = parse_program("begin while ¬ ¬ X > 0 do begin begin skip end end end", strict_bnf=True)
    w = res.ast.body
    assert isinstance(w, While)
    assert isinstance(w.cond, NotBexp)
    assert isinstance(w.cond.operand, NotBexp)
    assert isinstance(w.body, Block)
    assert isinstance(w.body.body, Block)
    assert isinstance(w.body.body.body, Skip)


@pytest.mark.parametrize(
    ("source", "expected_code", "expected_line", "expected_col"),
    [
        ("", "E_SYNTAX_EMPTY", 1, 1),
        ("   \n  // only comment\n", "E_SYNTAX_EMPTY", 3, 1),
        ("R := 1", "E_SYNTAX_EXPECTED_BEGIN", 1, 1),
        ("begin end", "E_SYNTAX_EMPTY_BLOCK", 1, 7),
        ("begin R := 1", "E_SYNTAX_EXPECTED_END", 1, 13),
        ("begin\n  R := 1;\nend", "E_SYNTAX_TRAILING_SEMICOLON", 2, 9),
        ("begin R = 1 end", "E_SYNTAX_EXPECTED_ASSIGN", 1, 9),
        ("begin if X > 0 then skip end", "E_SYNTAX_EXPECTED_ELSE", 1, 26),
        ("begin if X > 0 then R := 1; Y := 2 else skip end", "E_SYNTAX_EXPECTED_ELSE", 1, 27),
        ("begin if X > 0 R := 1 else skip end", "E_SYNTAX_EXPECTED_THEN", 1, 16),
        ("begin while X > 0 R := 1 end", "E_SYNTAX_EXPECTED_DO", 1, 19),
        ("begin R := (1 + 2 end", "E_SYNTAX_UNCLOSED_PAREN", 1, 19),
        ("begin if (X > 0 then skip else skip end", "E_SYNTAX_UNCLOSED_PAREN", 1, 17),
        ("begin skip end extra", "E_SYNTAX_TRAILING_TOKENS", 1, 16),
        ("begin\n  R : 1\nend", "E_LEX_STRAY_COLON", 2, 5),
        ("begin R := 1 @ 2 end", "E_LEX_UNKNOWN_CHAR", 1, 14),
        ("begin (* unclosed\n skip end", "E_LEX_UNCLOSED_COMMENT", 1, 7),
        ("begin R := -X end", "E_SYNTAX_UNARY_MINUS", 1, 12),
        ("begin if X then skip else skip end", "E_SYNTAX_EXPECTED_CMP", 1, 12),
        ("begin R := 12abc end", "E_LEX_INVALID_NUMBER", 1, 12),
    ],
)
def test_negative_syntax_errors_and_exact_spans(
    source: str,
    expected_code: str,
    expected_line: int,
    expected_col: int,
) -> None:
    with pytest.raises(SiplSyntaxError) as exc_info:
        parse_program(source)
    diag = exc_info.value.diagnostic
    assert diag.code == expected_code
    assert diag.span.start.line == expected_line
    assert diag.span.start.column == expected_col
    formatted = diag.format_with_source(source)
    assert expected_code in formatted
    assert "^" in formatted


@pytest.mark.parametrize(
    "source",
    [
        "begin X := 7 div 2 end",
        "begin X := 7 mod 2 end",
        "begin if X >= 0 then skip else skip end",
        "begin if X < 0 then skip else skip end",
        "begin if X <= 0 then skip else skip end",
        "begin if X != 0 then skip else skip end",
        "begin if X = 0 and Y = 0 then skip else skip end",
        "begin if X = 0 or Y = 0 then skip else skip end",
        "begin if not X = 0 then skip else skip end",
    ],
)
def test_strict_bnf_rejects_extensions(source: str) -> None:
    with pytest.raises(SiplSyntaxError):
        parse_program(source, strict_bnf=True)


def test_state_parse_formats_and_algebra_operations() -> None:
    s1 = State.parse("M=8, N=16")
    s2 = State.parse("[M ↦ 3, X ↦ 4, Y ↦ 2]")
    s3 = State.parse("[M -> 3, N -> 16, X -> 4, Y -> 2]")
    empty = State.parse("")
    assert len(empty) == 0
    assert State.parse("[]") == empty

    overlaid = s1.overlay(s2)
    assert overlaid == s3
    assert overlaid.format_course() == "[M ↦ 3, N ↦ 16, X ↦ 4, Y ↦ 2]"
    assert s1["M"] == 8
    assert s1.get("X") is None

    sup = State.parse("[M ↦ 8, X ↦ 4, Y ↦ 2, N ↦ 16]")
    assert s1.is_substate_of(sup)
    assert not overlaid.is_substate_of(sup)


@pytest.mark.parametrize("bad_state", ["X", "[X=5", "X=abc", "123=5"])
def test_state_parse_invalid_raises(bad_state: str) -> None:
    with pytest.raises((StateParseError, ValueError)):
        State.parse(bad_state)


def test_interpreter_power_program_and_trace() -> None:
    parsed = parse_program(POWER_PROGRAM)
    init = State.parse("[X ↦ 5, Y ↦ 2]")
    result = run_program(parsed.ast, init)
    assert result.is_defined
    assert result.status == "finished"
    assert result.final_state is not None
    assert result.final_state["R"] == 25
    assert result.final_state["Y"] == 0
    assert result.final_state["X"] == 5

    event_types = [e.event_type for e in result.trace.events]
    assert "BeforeStatement" in event_types
    assert "AfterStatement" in event_types
    assert "VariableChanged" in event_types
    assert "ConditionEvaluated" in event_types
    assert event_types[-1] == "ProgramFinished"
    assert result.to_dict()["final_state"] == {"X": 5, "Y": 0, "R": 25}


def test_interpreter_gcd_and_div_mod_programs() -> None:
    gcd_ast = parse_program(GCD_PROGRAM, strict_bnf=True).ast
    res = run_program(gcd_ast, State.parse("M=48, N=18"))
    assert res.is_defined and res.final_state is not None
    assert res.final_state["M"] == 6
    assert res.final_state["N"] == 6

    div_src = """begin
        Q := X div Y;
        Rem := X mod Y
    end"""
    div_res = run_program(parse_program(div_src).ast, State.parse("X=17, Y=5"))
    assert div_res.is_defined and div_res.final_state is not None
    assert div_res.final_state["Q"] == 3
    assert div_res.final_state["Rem"] == 2


def test_interpreter_undefined_behaviors_explicit() -> None:
    inf_ast = parse_program("begin while 1 = 1 do skip end").ast
    inf_res = run_program(inf_ast, State(), max_steps=10)
    assert not inf_res.is_defined
    assert inf_res.status == "undefined"
    assert inf_res.final_state is None
    assert inf_res.error_code == "E_MAX_STEPS"
    assert inf_res.trace.events[-1].event_type == "ProgramUndefined"

    undef_ast = parse_program("begin R := Z + 1 end").ast
    undef_res = run_program(undef_ast, State.parse("X=1"))
    assert undef_res.status == "undefined"
    assert undef_res.error_code == "E_UNDEFINED_VAR"

    div0_ast = parse_program("begin R := 10 div 0 end").ast
    div0_res = run_program(div0_ast, State())
    assert div0_res.status == "undefined"
    assert div0_res.error_code == "E_DIV_ZERO"

    mod0_ast = parse_program("begin R := 10 mod 0 end").ast
    mod0_res = run_program(mod0_ast, State())
    assert mod0_res.status == "undefined"
    assert mod0_res.error_code == "E_MOD_ZERO"


def test_standalone_eval_aexp_bexp_errors() -> None:
    expr = parse_program("begin R := X + 1 end").ast.body
    assert isinstance(expr, Assign)
    assert eval_aexp(expr.expr, State({"X": 4})) == 5
    with pytest.raises(SiplRuntimeError):
        eval_aexp(expr.expr, State())

    cond_stm = parse_program("begin if A = 1 or B = 2 then skip else skip end").ast.body
    assert isinstance(cond_stm, If)
    assert eval_bexp(cond_stm.cond, State({"A": 1, "B": 0})) is True
    with pytest.raises(SiplRuntimeError):
        eval_bexp(cond_stm.cond, State({"A": 1}))
