"""Integration tests for SIPL CLI and full end-to-end pipeline."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

from sipl import (
    build_semantic_term,
    evaluate_semantic_term,
    parse_program,
    prove_program,
    render_pipeline_html,
)
from sipl.cli import main
from sipl.interpreter import State

REPO_ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_DIR = REPO_ROOT / "examples"
SPECS_DIR = EXAMPLES_DIR / "specs"
INVALID_DIR = EXAMPLES_DIR / "invalid"


def test_cli_parse_and_check_text_and_json(capsys: pytest.CaptureFixture[str]) -> None:
    p_file = str(EXAMPLES_DIR / "01_power_xy.sipl")

    rc = main(["parse", p_file])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Program" in out
    assert "Синтаксична перевірка крони дерева: OK" in out

    rc_json = main(["parse", p_file, "--json"])
    assert rc_json == 0
    data = json.loads(capsys.readouterr().out)
    assert data["is_crown_valid"] is True
    assert data["leaf_count"] == 24
    assert data["ast"]["kind"] == "Program"
    assert data["parse_tree"]["rule_name"] == "NP1"

    rc_chk = main(["check", p_file, "--strict-bnf"])
    assert rc_chk == 0
    chk_out = capsys.readouterr().out
    assert "OK:" in chk_out
    assert "leaves=24" in chk_out

    rc_chk_json = main(["check", p_file, "--json"])
    assert rc_chk_json == 0
    chk_data = json.loads(capsys.readouterr().out)
    assert chk_data["valid"] is True
    assert chk_data["is_crown_valid"] is True


def test_cli_syntax_error_and_strict_bnf_diagnostics(capsys: pytest.CaptureFixture[str]) -> None:
    bad_file = str(INVALID_DIR / "syntax_missing_end.sipl")

    rc = main(["check", bad_file])
    assert rc == 1
    captured = capsys.readouterr()
    assert "E_SYNTAX_EXPECTED_END" in captured.err
    assert "line" in captured.err

    rc_json = main(["check", bad_file, "--json"])
    assert rc_json == 1
    err_data = json.loads(capsys.readouterr().out)
    assert err_data["valid"] is False
    assert err_data["error_code"] == "E_SYNTAX_EXPECTED_END"
    assert "span" in err_data["diagnostic"]

    div_file = str(EXAMPLES_DIR / "02_div_xy.sipl")
    rc_strict = main(["check", div_file, "--strict-bnf", "--json"])
    assert rc_strict == 1
    strict_data = json.loads(capsys.readouterr().out)
    assert strict_data["valid"] is False


def test_cli_term_formats(capsys: pytest.CaptureFixture[str]) -> None:
    p_file = str(EXAMPLES_DIR / "01_power_xy.sipl")

    assert main(["term", p_file, "--format", "unicode"]) == 0
    u_out = capsys.readouterr().out.strip()
    assert "AS^R(1̄)" in u_out
    assert "WH(" in u_out

    assert main(["term", p_file, "--format", "latex"]) == 0
    l_out = capsys.readouterr().out.strip()
    assert r"\mathrm{WH}" in l_out

    assert main(["term", p_file, "--format", "derivation"]) == 0
    d_out = capsys.readouterr().out
    assert "NS_Prog" in d_out
    assert "NS_Stm_Wh" in d_out
    assert "LaTeX:" in d_out

    assert main(["term", p_file, "--json"]) == 0
    j_data = json.loads(capsys.readouterr().out)
    assert "unicode" in j_data
    assert "latex" in j_data
    assert len(j_data["steps"]) > 0


def test_cli_eval_defined_and_undefined(capsys: pytest.CaptureFixture[str]) -> None:
    p_file = str(EXAMPLES_DIR / "01_power_xy.sipl")

    rc = main(["eval", p_file, "--state", "X=5, Y=2"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "R ↦ 25" in out
    assert "Y ↦ 0" in out
    assert "NumItWH" in out

    rc_json = main(["eval", p_file, "--state", "X=3, Y=4", "--json"])
    assert rc_json == 0
    data = json.loads(capsys.readouterr().out)
    assert data["defined"] is True
    assert data["final_state"] == {"X": 3, "Y": 0, "R": 81}
    assert len(data["loop_iterations"]) == 4

    rc_undef = main(["eval", p_file, "--state", "X=5", "--json"])
    assert rc_undef == 1
    undef_data = json.loads(capsys.readouterr().out)
    assert undef_data["defined"] is False
    assert undef_data["error_code"] == "E_UNDEFINED_VAR"

    inf_file = str(INVALID_DIR / "infinite_loop.sipl")
    rc_inf = main(["eval", inf_file, "--state", "X=2, Y=1", "--max-iterations", "5"])
    assert rc_inf == 1
    inf_out = capsys.readouterr().out
    assert "↑" in inf_out


def test_cli_prove_specs_options_and_exit_codes(capsys: pytest.CaptureFixture[str]) -> None:
    for prog_name, spec_name in [
        ("01_power_xy.sipl", "01_power_xy.json"),
        ("02_div_xy.sipl", "02_div_xy.json"),
        ("04_arith_prog_sum.sipl", "04_arith_prog_sum.json"),
        ("06_sub_minus_one.sipl", "06_sub_minus_one.json"),
    ]:
        rc = main(
            [
                "prove",
                str(EXAMPLES_DIR / prog_name),
                "--spec",
                str(SPECS_DIR / spec_name),
                "--json",
            ]
        )
        assert rc == 0
        rep = json.loads(capsys.readouterr().out)
        assert rep["status"] == "proved", f"{prog_name} gave {rep}"

    rc_buggy = main(
        [
            "prove",
            str(INVALID_DIR / "buggy_power_init.sipl"),
            "--spec",
            str(SPECS_DIR / "01_power_xy.json"),
        ]
    )
    assert rc_buggy == 1
    buggy_out = capsys.readouterr().out
    assert "disproved" in buggy_out
    assert "Знайдені контрприклади" in buggy_out

    rc_hyp = main(
        [
            "prove",
            str(EXAMPLES_DIR / "01_power_xy.sipl"),
            "--precondition",
            "X > 0 and Y > 0",
            "--postcondition",
            "R == x**y",
            "--hypothesis",
            "X=x, Y=y-k, R=x**k",
            "--mode",
            "forward_induction",
            "--json",
        ]
    )
    assert rc_hyp == 0
    hyp_data = json.loads(capsys.readouterr().out)
    assert hyp_data["status"] == "proved"
    assert hyp_data["hypothesis_source"] == "user"

    rc_gcd = main(
        [
            "prove",
            str(EXAMPLES_DIR / "03_gcd_euclid.sipl"),
            "--precondition",
            "M > 0 and N > 0",
            "--invariant",
            "M > 0 and N > 0",
            "--postcondition",
            "M = N",
            "--json",
        ]
    )
    assert rc_gcd == 0
    gcd_data = json.loads(capsys.readouterr().out)
    assert gcd_data["status"] in ("partial", "unsupported")
    assert len(gcd_data["limitations"]) > 0


def test_cli_run_and_trace(capsys: pytest.CaptureFixture[str]) -> None:
    div_file = str(EXAMPLES_DIR / "02_div_xy.sipl")

    assert main(["run", div_file, "--state", "X=17, Y=5"]) == 0
    run_text = capsys.readouterr().out
    assert "Final state:   [X ↦ 2, Y ↦ 5, R ↦ 3]" in run_text

    assert main(["run", div_file, "--state", "X=17, Y=5", "--json"]) == 0
    run_data = json.loads(capsys.readouterr().out)
    assert run_data["is_defined"] is True
    assert run_data["final_state"] == {"X": 2, "Y": 5, "R": 3}

    assert main(["trace", div_file, "--state", "X=17, Y=5"]) == 0
    tr_text = capsys.readouterr().out
    assert "Trace (" in tr_text
    assert "Final state: [X ↦ 2, Y ↦ 5, R ↦ 3]" in tr_text

    assert main(["trace", div_file, "--state", "X=17, Y=5", "--json"]) == 0
    tr_data = json.loads(capsys.readouterr().out)
    assert tr_data["is_defined"] is True
    assert len(tr_data["trace"]["events"]) > 0


def test_cli_visualize_all_formats_and_pipeline_integration(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    p_file = str(EXAMPLES_DIR / "01_power_xy.sipl")

    svg_out = tmp_path / "pt.svg"
    assert main(["visualize", p_file, "--format", "svg", "-o", str(svg_out)]) == 0
    _ = capsys.readouterr()
    svg_root = ET.fromstring(svg_out.read_text(encoding="utf-8"))
    assert svg_root.tag == "{http://www.w3.org/2000/svg}svg"

    html_out = tmp_path / "pipeline.html"
    assert (
        main(
            [
                "visualize",
                p_file,
                "--format",
                "html",
                "--state",
                "X=2, Y=3",
                "--spec",
                str(SPECS_DIR / "01_power_xy.json"),
                "-o",
                str(html_out),
                "--json",
            ]
        )
        == 0
    )
    meta = json.loads(capsys.readouterr().out)
    assert meta["format"] == "html"
    html_text = html_out.read_text(encoding="utf-8")
    assert "<!DOCTYPE html>" in html_text
    assert "NS_Prog" in html_text
    assert "AF_AS" in html_text
    assert "База індукції (k = 0)" in html_text
    assert "x^k" in html_text
    assert "R ↦ 8" in html_text


def test_render_pipeline_html_with_real_semantic_eval_and_proof_objects() -> None:
    src = (EXAMPLES_DIR / "01_power_xy.sipl").read_text(encoding="utf-8")
    parsed = parse_program(src)
    sem_term = build_semantic_term(parsed.ast, source_program=src)
    eval_res = evaluate_semantic_term(sem_term.term, State({"X": 2, "Y": 3}))
    proof_res = prove_program(
        parsed.ast,
        precondition="Y >= 0",
        postcondition="R = X_0 ^ Y_0",
        mode="hybrid",
    )
    html_doc = render_pipeline_html(
        parsed,
        semantic_term=sem_term,
        eval_result=eval_res,
        proof_result=proof_res,
    )
    assert "NS_Prog" in html_doc
    assert "sem_S(R := 1)" in html_doc
    assert "AF_AS" in html_doc
    assert "AF_WH" in html_doc
    assert "База індукції (k = 0)" in html_doc
    assert "proved" in html_doc
    assert "↑ (undefined)" not in html_doc


def test_cli_subprocess_utf8_entrypoint() -> None:
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "sipl.cli",
            "eval",
            str(EXAMPLES_DIR / "01_power_xy.sipl"),
            "--state",
            "X=2, Y=3",
        ],
        cwd=str(REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    assert proc.returncode == 0
    assert "R ↦ 8" in proc.stdout
    assert "NumItWH" in proc.stdout
