"""Tests for SIPL semantic terms and step-by-step derivation."""

from __future__ import annotations

import json
from typing import Any, cast

import pytest

from sipl import (
    Assign,
    ASTNode,
    If,
    Number,
    SiplSemanticError,
    parse_program,
)
from sipl.semantics import (
    AssignTerm,
    BlockTerm,
    ConstNumTerm,
    DerefTerm,
    DerivationStep,
    IdTerm,
    IfTerm,
    SeqTerm,
    SuperposAexpTerm,
    SuperposBoolTerm,
    SuperposCmpTerm,
    TermBuildResult,
    WhileTerm,
    build_aexp_term,
    build_bexp_term,
    build_semantic_term,
    build_stm_term,
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


def test_golden_power_program_semantic_term() -> None:
    prog = parse_program(POWER_PROGRAM).ast
    result = build_semantic_term(prog, source_program=POWER_PROGRAM)
    assert isinstance(result, TermBuildResult)
    assert isinstance(result.term, SeqTerm)
    expected = (
        "AS^R(1\u0304) \u00b7 WH(S^2(gr, Y\u21d2, 0\u0304), "
        "AS^R(S^2(mult, R\u21d2, X\u21d2)) \u00b7 AS^Y(S^2(sub, Y\u21d2, 1\u0304)))"
    )
    assert result.format_unicode() == expected
    assert result.term.format_unicode() == expected

    rule_names = [step.rule_name for step in result.steps]
    assert rule_names[0] == "NS_Prog"
    assert "NS_Stm_Seq" in rule_names
    assert "NS_Stm_As" in rule_names
    assert "NS_Stm_Wh" in rule_names
    assert "NS_Stm_BE" in rule_names
    assert "NS_B_gr" in rule_names
    assert "NS_A_Mult" in rule_names
    assert "NS_A_Sub" in rule_names
    assert "NS_A_Var" in rule_names
    assert "NS_A_Num" in rule_names


def test_golden_div_program_semantic_term() -> None:
    prog = parse_program(DIV_PROGRAM).ast
    result = build_semantic_term(prog)
    expected = (
        "AS^R(0\u0304) \u00b7 WH(S^2(gre, X\u21d2, Y\u21d2), "
        "AS^X(S^2(sub, X\u21d2, Y\u21d2)) \u00b7 AS^R(S^2(add, R\u21d2, 1\u0304)))"
    )
    assert result.format_unicode() == expected
    rule_names = [step.rule_name for step in result.steps]
    assert "NS_B_gre" in rule_names
    assert "NS_A_Add" in rule_names


def test_golden_aexp_precedence_x_plus_y_times_z() -> None:
    prog = parse_program("begin _tmp := X + Y * Z end").ast
    assert isinstance(prog.body, Assign)
    res = build_semantic_term(prog.body.expr)
    assert res.format_unicode() == "S^2(add, X\u21d2, S^2(mult, Y\u21d2, Z\u21d2))"
    assert [s.rule_name for s in res.steps] == [
        "NS_A_Add",
        "NS_A_Var",
        "NS_A_Mult",
        "NS_A_Var",
        "NS_A_Var",
    ]


def test_skip_and_if_then_else_and_gcd() -> None:
    skip_prog = parse_program("begin skip end").ast
    skip_res = build_semantic_term(skip_prog)
    assert isinstance(skip_res.term, IdTerm)
    assert skip_res.format_unicode() == "id"
    assert skip_res.format_latex() == "\\mathrm{id}"
    assert [s.rule_name for s in skip_res.steps] == ["NS_Prog", "NS_Stm_skip"]

    if_prog = parse_program("begin if X > 0 then Y := 1 else Y := 2 end").ast
    if_res = build_semantic_term(if_prog)
    assert isinstance(if_res.term, IfTerm)
    assert if_res.format_unicode() == "IF(S^2(gr, X\u21d2, 0\u0304), AS^Y(1\u0304), AS^Y(2\u0304))"
    assert [s.rule_name for s in if_res.steps] == [
        "NS_Prog",
        "NS_Stm_If",
        "NS_B_gr",
        "NS_A_Var",
        "NS_A_Num",
        "NS_Stm_As",
        "NS_A_Num",
        "NS_Stm_As",
        "NS_A_Num",
    ]

    gcd_prog = parse_program(GCD_PROGRAM).ast
    gcd_res = build_semantic_term(gcd_prog)
    assert gcd_res.format_unicode() == (
        "WH(S^1(neg, S^2(eq, M\u21d2, N\u21d2)), "
        "IF(S^2(gr, M\u21d2, N\u21d2), "
        "AS^M(S^2(sub, M\u21d2, N\u21d2)), AS^N(S^2(sub, N\u21d2, M\u21d2))))"
    )
    assert "NS_B_neg" in [s.rule_name for s in gcd_res.steps]
    assert "NS_B_eq" in [s.rule_name for s in gcd_res.steps]


def test_extended_aexp_div_mod_and_negative_and_parens() -> None:
    prog = parse_program("begin R := (X div 2) + (Y mod -3) end").ast
    res = build_semantic_term(prog)
    assert res.format_unicode() == (
        "AS^R(S^2(add, S^2(div, X\u21d2, 2\u0304), S^2(mod, Y\u21d2, -3\u0304)))"
    )
    rules = [s.rule_name for s in res.steps]
    assert rules.count("NS_A_Par") == 2
    assert "NS_A_Div" in rules
    assert "NS_A_Mod" in rules
    assert "NS_A_Num" in rules

    neg_num_prog = parse_program("begin X := -1; Y := 12 end").ast
    neg_res = build_semantic_term(neg_num_prog)
    assert neg_res.format_unicode() == "AS^X(-1\u0304) \u00b7 AS^Y(12\u0304)"


def test_all_bexp_operators_and_parens() -> None:
    prog = parse_program(
        "begin if ((A < B) and (C <= D)) or (E != F) then skip else X := 0 end"
    ).ast
    res = build_semantic_term(prog)
    assert res.format_unicode() == (
        "IF(S^2(or, S^2(and, S^2(less, A\u21d2, B\u21d2), S^2(leq, C\u21d2, D\u21d2)), "
        "S^2(neq, E\u21d2, F\u21d2)), id, AS^X(0\u0304))"
    )
    rules = {s.rule_name for s in res.steps}
    assert {"NS_B_Par", "NS_B_or", "NS_B_and", "NS_B_less", "NS_B_leq", "NS_B_neq"} <= rules


def test_seq_associativity_and_nested_block_parens() -> None:
    flat_prog = parse_program("begin X := 1; Y := 2; Z := 3 end").ast
    flat_res = build_semantic_term(flat_prog)
    assert flat_res.format_unicode() == "AS^X(1\u0304) \u00b7 AS^Y(2\u0304) \u00b7 AS^Z(3\u0304)"

    nested_prog = parse_program("begin X := 1; begin Y := 2; Z := 3 end end").ast
    nested_res = build_semantic_term(nested_prog)
    assert nested_res.format_unicode() == (
        "AS^X(1\u0304) \u00b7 (AS^Y(2\u0304) \u00b7 AS^Z(3\u0304))"
    )

    assert isinstance(nested_res.term, SeqTerm)
    assert isinstance(nested_res.term.right, BlockTerm)
    assert nested_res.term.right.format_unicode() == "AS^Y(2\u0304) \u00b7 AS^Z(3\u0304)"


def test_helpers_build_stm_aexp_bexp_and_error() -> None:
    prog = parse_program("begin if X > 0 then X := X - 1 else skip end").ast
    stm_res = build_stm_term(prog.body)
    assert isinstance(stm_res.term, IfTerm)
    assert stm_res.steps[0].rule_name == "NS_Stm_If"

    assert isinstance(prog.body, If)
    bexp_res = build_bexp_term(prog.body.cond)
    assert isinstance(bexp_res.term, SuperposCmpTerm)
    assert bexp_res.format_unicode() == "S^2(gr, X\u21d2, 0\u0304)"

    aexp_res = build_aexp_term(Number(value=42, span=prog.span, node_id="n1"))
    assert isinstance(aexp_res.term, ConstNumTerm)
    assert aexp_res.format_unicode() == "42\u0304"

    bad_node = ASTNode(span=prog.span, node_id="bad")
    with pytest.raises(SiplSemanticError):
        build_semantic_term(cast(Any, bad_node))


def test_latex_derivation_text_and_json_serialization() -> None:
    prog = parse_program(POWER_PROGRAM).ast
    res = build_semantic_term(prog, source_program=POWER_PROGRAM)

    latex = res.format_latex()
    assert latex == (
        "AS^{R}(\\overline{1}) \\cdot \\mathrm{WH}("
        "S^{2}(\\mathrm{gr}, Y\\Rightarrow, \\overline{0}), "
        "AS^{R}(S^{2}(\\mathrm{mult}, R\\Rightarrow, X\\Rightarrow)) \\cdot "
        "AS^{Y}(S^{2}(\\mathrm{sub}, Y\\Rightarrow, \\overline{1})))"
    )

    deriv_text = res.format_derivation_text()
    assert "Крок 1 [NS_Prog]:" in deriv_text
    assert "Отриманий семантичний терм:" in deriv_text

    payload = res.to_dict()
    encoded = json.dumps(payload, ensure_ascii=False)
    decoded = json.loads(encoded)
    assert decoded["unicode"] == res.format_unicode()
    assert decoded["latex"] == latex
    assert decoded["term"]["kind"] == "SeqTerm"
    assert len(decoded["steps"]) == len(res.steps)
    for step_dict, step_obj in zip(decoded["steps"], res.steps, strict=True):
        assert isinstance(step_obj, DerivationStep)
        assert step_dict["step_index"] == step_obj.step_index
        assert step_dict["rule_name"] == step_obj.rule_name
        assert step_dict["ast_node_id"] is not None
        assert step_dict["span"] is not None


def test_manual_term_construction_and_term_ids() -> None:
    manual = AssignTerm(
        var="R",
        expr=SuperposAexpTerm(
            op_name="add",
            args=[DerefTerm(var="X"), ConstNumTerm(value=1)],
        ),
    )
    assert manual.format_unicode() == "AS^R(S^2(add, X\u21d2, 1\u0304))"
    assert manual.format_latex() == "AS^{R}(S^{2}(\\mathrm{add}, X\\Rightarrow, \\overline{1}))"
    neg_bool = SuperposBoolTerm(
        op_name="neg",
        args=[SuperposCmpTerm(op_name="eq", left=DerefTerm(var="X"), right=ConstNumTerm(value=0))],
    )
    assert neg_bool.format_unicode() == "S^1(neg, S^2(eq, X\u21d2, 0\u0304))"
    assert WhileTerm(cond=neg_bool, body=IdTerm()).format_unicode() == (
        "WH(S^1(neg, S^2(eq, X\u21d2, 0\u0304)), id)"
    )
