"""Tests for SIPL visualization exporters and course examples."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from sipl import SiplSyntaxError, State, parse_program, run_program
from sipl.visualization import (
    compare_parse_tree_and_ast,
    render_ast_dot,
    render_ast_json,
    render_ast_svg,
    render_ast_text,
    render_comparison_html,
    render_parse_tree_dot,
    render_parse_tree_json,
    render_parse_tree_svg,
    render_parse_tree_text,
    render_pipeline_html,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_DIR = REPO_ROOT / "examples"
SPECS_DIR = EXAMPLES_DIR / "specs"
INVALID_DIR = EXAMPLES_DIR / "invalid"

EXPECTED_EXAMPLES = [
    "01_power_xy.sipl",
    "02_div_xy.sipl",
    "03_gcd_euclid.sipl",
    "04_arith_prog_sum.sipl",
    "05_factorial.sipl",
    "06_sub_minus_one.sipl",
    "07_parity_check.sipl",
    "08_log2_floor.sipl",
]


@pytest.mark.parametrize("filename", EXPECTED_EXAMPLES)
def test_course_example_parses_with_valid_crown(filename: str) -> None:
    src = (EXAMPLES_DIR / filename).read_text(encoding="utf-8")
    res = parse_program(src)
    assert res.is_crown_valid is True
    assert len(res.parse_tree.leaves()) > 0


def test_course_examples_execution_semantics() -> None:
    cases: list[tuple[str, dict[str, int], dict[str, int]]] = [
        ("01_power_xy.sipl", {"X": 2, "Y": 5}, {"R": 32, "Y": 0}),
        ("02_div_xy.sipl", {"X": 17, "Y": 5}, {"R": 3, "X": 2}),
        ("03_gcd_euclid.sipl", {"M": 48, "N": 18}, {"M": 6, "N": 6}),
        ("04_arith_prog_sum.sipl", {"N": 4}, {"S": 20, "I": 4}),
        ("05_factorial.sipl", {"N": 5}, {"R": 120, "N": 0}),
        ("06_sub_minus_one.sipl", {"X": 10, "Y": 3}, {"R": 7, "Y": 0}),
        ("07_parity_check.sipl", {"N": 5}, {"R": 0, "N": 0}),
        ("07_parity_check.sipl", {"N": 6}, {"R": 1, "N": 0}),
        ("08_log2_floor.sipl", {"N": 19}, {"R": 4, "N": 1}),
    ]
    for filename, init_map, expected in cases:
        res = parse_program((EXAMPLES_DIR / filename).read_text(encoding="utf-8"))
        exec_res = run_program(res.ast, State(init_map))
        assert exec_res.is_defined, f"{filename} failed: {exec_res.error}"
        assert exec_res.final_state is not None
        for var, val in expected.items():
            assert exec_res.final_state[var] == val


@pytest.mark.parametrize(
    "spec_name",
    [
        "01_power_xy.json",
        "02_div_xy.json",
        "04_arith_prog_sum.json",
        "06_sub_minus_one.json",
    ],
)
def test_proof_specs_match_programs(spec_name: str) -> None:
    spec = json.loads((SPECS_DIR / spec_name).read_text(encoding="utf-8"))
    required_keys = (
        "precondition",
        "postcondition",
        "hypothesis",
        "backward_invariants",
        "test_domains",
    )
    for key in required_keys:
        assert key in spec
    prog_path = REPO_ROOT / spec["program"]
    parsed = parse_program(prog_path.read_text(encoding="utf-8"))
    assert parsed.is_crown_valid
    for domain in spec["test_domains"]:
        exec_res = run_program(parsed.ast, State(domain["input"]))
        assert exec_res.is_defined
        assert exec_res.final_state is not None
        for k, v in domain["expected"].items():
            assert exec_res.final_state[k] == v


def test_invalid_and_buggy_examples() -> None:
    with pytest.raises(SiplSyntaxError):
        parse_program((INVALID_DIR / "syntax_missing_end.sipl").read_text(encoding="utf-8"))
    with pytest.raises(SiplSyntaxError):
        parse_program((INVALID_DIR / "syntax_bad_assign.sipl").read_text(encoding="utf-8"))

    buggy_power = parse_program((INVALID_DIR / "buggy_power_init.sipl").read_text(encoding="utf-8"))
    assert buggy_power.is_crown_valid
    buggy_exec = run_program(buggy_power.ast, State({"X": 2, "Y": 5}))
    assert buggy_exec.is_defined and buggy_exec.final_state is not None
    assert buggy_exec.final_state["R"] == 0

    inf_loop = parse_program((INVALID_DIR / "infinite_loop.sipl").read_text(encoding="utf-8"))
    assert inf_loop.is_crown_valid
    inf_exec = run_program(inf_loop.ast, State({"X": 2, "Y": 1}), max_steps=100)
    assert not inf_exec.is_defined
    assert inf_exec.error_code == "E_MAX_STEPS"


def test_render_parse_tree_text_power_program() -> None:
    src = (EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8")
    res = parse_program(src)
    text = render_parse_tree_text(res)

    for non_term in ("<програма>", "<оператор>", "<вираз>", "<умова>", "<змінна>", "<число>"):
        assert non_term in text
    for rule in ("NP1", "NS1", "NS2", "NS4", "NS5", "NA1", "NA2", "NA4", "NA5", "NB2", "NV", "NN"):
        assert rule in text
    for idx in range(1, 25):
        assert f"[{idx}]" in text
    assert "[1:1]" in text
    assert res.crown_text in text
    assert res.parse_tree.numbered_crown() in text
    assert "Синтаксична перевірка крони дерева: OK" in text

    res_bad = parse_program(src)
    res_bad.is_crown_valid = False
    assert "Синтаксична перевірка крони дерева: MISMATCH" in render_parse_tree_text(res_bad)


def test_render_parse_tree_json_structure() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    data = json.loads(render_parse_tree_json(res))
    assert data["crown_text"] == res.crown_text
    assert data["is_crown_valid"] is True
    assert data["leaf_count"] == 24
    assert data["tree"]["rule_name"] == "NP1"
    assert "span" in data["tree"]
    assert "ast_node_id" in data["tree"]


def test_render_parse_tree_dot() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    dot = render_parse_tree_dot(res)
    assert dot.startswith("digraph SIPLParseTree {")
    assert dot.rstrip().endswith("}")
    assert "[NP1]" in dot
    assert "[1] begin" in dot
    assert "[24] end" in dot
    assert "->" in dot


def _assert_svg_nodes_non_overlapping(svg_root: ET.Element) -> None:
    ns = "{http://www.w3.org/2000/svg}"
    boxes: list[tuple[float, float, float, float]] = []
    for g in svg_root.findall(f".//{ns}g[@class='sipl-node']"):
        rect = g.find(f"{ns}rect")
        assert rect is not None
        x = float(rect.attrib["x"])
        y = float(rect.attrib["y"])
        w = float(rect.attrib["width"])
        h = float(rect.attrib["height"])
        for bx, by, bw, bh in boxes:
            overlap_x = x < bx + bw and x + w > bx
            overlap_y = y < by + bh and y + h > by
            assert not (overlap_x and overlap_y), (
                f"Overlapping SVG nodes: {(x, y, w, h)} vs {(bx, by, bw, bh)}"
            )
        boxes.append((x, y, w, h))


def test_render_parse_tree_svg_valid_xml_and_all_24_leaves() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    svg = render_parse_tree_svg(res)
    root = ET.fromstring(svg)
    assert root.tag == "{http://www.w3.org/2000/svg}svg"
    _assert_svg_nodes_non_overlapping(root)

    for idx in range(1, 25):
        assert f"[{idx}]" in svg
    assert "NP1" in svg
    assert "Синтаксична перевірка крони дерева: OK" in svg
    assert "<title>" in svg


def test_ast_exporters_text_json_dot_svg() -> None:
    res = parse_program((EXAMPLES_DIR / "03_gcd_euclid.sipl").read_text(encoding="utf-8"))

    ast_text = render_ast_text(res)
    assert "Program" in ast_text
    assert "While" in ast_text
    assert "NotBexp" in ast_text
    assert "If" in ast_text

    ast_json = json.loads(render_ast_json(res))
    assert ast_json["kind"] == "Program"
    assert ast_json["body"]["kind"] == "While"

    ast_dot = render_ast_dot(res)
    assert ast_dot.startswith("digraph SIPLAST {")
    assert "While" in ast_dot
    assert 'label="cond"' in ast_dot

    ast_svg = render_ast_svg(res)
    root = ET.fromstring(ast_svg)
    assert root.tag == "{http://www.w3.org/2000/svg}svg"
    _assert_svg_nodes_non_overlapping(root)
    assert res.ast.node_id in ast_svg


def test_compare_parse_tree_and_ast_and_html() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    cmp_data = compare_parse_tree_and_ast(res)

    assert cmp_data["parse_tree_terminal_count"] == 24
    assert cmp_data["parse_tree_node_count"] > cmp_data["ast_node_count"]
    assert cmp_data["parse_tree_depth"] >= cmp_data["ast_depth"]
    assert res.ast.node_id in cmp_data["ast_to_parse_tree_ids"]
    assert "begin" in cmp_data["removed_token_texts"]
    assert ";" in cmp_data["removed_token_texts"]

    comp_html = render_comparison_html(res)
    assert "<!DOCTYPE html>" in comp_html
    assert 'id="sipl-parse-tree-svg"' in comp_html
    assert 'id="sipl-ast-svg"' in comp_html
    assert 'class="src-tok"' in comp_html
    assert "highlightSelection" in comp_html
    comp_no_svg_ns = comp_html.replace("http://www.w3.org/2000/svg", "")
    assert "https://" not in comp_no_svg_ns and "http://" not in comp_no_svg_ns


@dataclass
class _MockSemanticStep:
    rule: str
    ast_node_id: str
    source_fragment: str
    term: str
    explanation: str


class _MockSemanticTerm:
    def __init__(self, ast_id: str) -> None:
        self._ast_id = ast_id
        self.steps = [
            _MockSemanticStep(
                rule="NS_2",
                ast_node_id=ast_id,
                source_fragment="R := 1; while Y > 0 do ...",
                term="S_stm[S1; S2] = S_stm[S2] ∘ S_stm[S1]",
                explanation="Sequential composition",
            )
        ]

    def format_unicode(self) -> str:
        return "λst. fix(F)(st ∇ [R ↦ 1])"

    def format_latex(self) -> str:
        return r"\lambda st.\ \mathrm{fix}(F)(st \nabla [R \mapsto 1])"


class _MockProofResult:
    status = "proved"
    precondition = "Y >= 0"
    postcondition = "R = X_0 ^ Y_0"
    hypothesis = "R * X ^ Y = X_0 ^ Y_0 and Y >= 0"
    explanation_text = "All 3 backward verification conditions discharged."

    def to_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "is_valid": True,
            "precondition": self.precondition,
            "postcondition": self.postcondition,
            "hypothesis": self.hypothesis,
            "explanation_text": self.explanation_text,
            "verification_conditions": [
                {
                    "name": "VC1 (Loop Exit)",
                    "formula": "Y = 0 => R = X_0 ^ Y_0",
                    "status": "valid",
                    "ast_node_id": "ast_1",
                }
            ],
        }


def test_render_pipeline_html_without_optional_objects() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    html_out = render_pipeline_html(res)
    assert "<!DOCTYPE html>" in html_out
    assert "1. Source Code" in html_out
    assert "2. Concrete Parse Tree" in html_out
    assert "3. Typed Abstract Syntax Tree (AST)" in html_out
    assert "4. Semantic Term &amp; NS Derivation" in html_out
    assert "5. State Transitions (AF) &amp; Correctness Proof" in html_out
    assert "Semantic term not provided" in html_out
    assert "Evaluation trace not provided" in html_out
    assert "No correctness proof attached" in html_out
    html_no_svg_ns = html_out.replace("http://www.w3.org/2000/svg", "")
    assert "https://" not in html_no_svg_ns and "http://" not in html_no_svg_ns


def test_render_pipeline_html_with_duck_typed_and_runtime_objects() -> None:
    res = parse_program((EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8"))
    exec_res = run_program(res.ast, State({"X": 2, "Y": 3}))
    sem_term = _MockSemanticTerm(res.ast.body.node_id)
    proof_res = _MockProofResult()

    html_out = render_pipeline_html(
        res,
        semantic_term=sem_term,
        eval_result=exec_res,
        proof_result=proof_res,
    )
    assert "λst. fix(F)(st ∇ [R ↦ 1])" in html_out
    assert r"\lambda st." in html_out
    assert "NS_2" in html_out
    assert "VariableChanged (Assign)" in html_out
    assert "R ↦ 8" in html_out
    assert "proved" in html_out
    assert "All 3 backward verification conditions discharged." in html_out
    assert "VC1 (Loop Exit)" in html_out
    assert f'data-ast-id="{res.ast.body.node_id}"' in html_out
