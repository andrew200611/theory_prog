"""Command-line interface for the SIPL Language Toolkit."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from sipl import __version__
from sipl.ast import Block, If, Seq, Stm, While
from sipl.diagnostics import SiplError, SiplRuntimeError, SiplSemanticError, SiplSyntaxError
from sipl.interpreter import State, StateParseError, run_program
from sipl.parser import ParseResult, parse_program
from sipl.semantics import (
    EvaluationResult,
    ProofReport,
    build_semantic_term,
    evaluate_semantic_term,
    prove_program,
)
from sipl.visualization import (
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


def _configure_utf8_streams() -> None:
    """Ensure stdout/stderr support Unicode symbols on Windows consoles."""
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if callable(reconfigure):
            try:
                reconfigure(encoding="utf-8", errors="replace")
            except OSError:
                pass


def _print_json(payload: Any) -> None:
    print(json.dumps(payload, ensure_ascii=False, indent=2))


def _emit_error(
    message: str,
    *,
    as_json: bool,
    code: str = "E_CLI",
    diagnostic: dict[str, Any] | None = None,
    formatted: str | None = None,
) -> int:
    if as_json:
        payload: dict[str, Any] = {
            "valid": False,
            "error_code": code,
            "error": message,
        }
        if diagnostic is not None:
            payload["diagnostic"] = diagnostic
        _print_json(payload)
    else:
        print(formatted if formatted is not None else f"Error [{code}]: {message}", file=sys.stderr)
    return 1


def _read_and_parse(
    file_path: str,
    *,
    strict_bnf: bool,
    as_json: bool,
) -> tuple[str, ParseResult] | None:
    path = Path(file_path)
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        _emit_error(f"Cannot read file '{file_path}': {exc}", as_json=as_json, code="E_IO")
        return None

    try:
        result = parse_program(source, strict_bnf=strict_bnf)
    except SiplSyntaxError as exc:
        _emit_error(
            str(exc),
            as_json=as_json,
            code=exc.diagnostic.code,
            diagnostic=exc.diagnostic.to_dict(),
            formatted=exc.diagnostic.format_with_source(source),
        )
        return None
    return source, result


def _parse_state_arg(raw_state: str, *, as_json: bool) -> State | None:
    try:
        return State.parse(raw_state)
    except StateParseError as exc:
        _emit_error(str(exc), as_json=as_json, code="E_STATE_PARSE")
        return None


def _parse_hypothesis_arg(raw_hyp: str) -> dict[str, str]:
    stripped = raw_hyp.strip()
    if stripped.startswith("{"):
        loaded = json.loads(stripped)
        if not isinstance(loaded, dict):
            raise ValueError("JSON hypothesis must be an object mapping variable names to formulas")
        return {str(k): str(v) for k, v in loaded.items()}

    mapping: dict[str, str] = {}
    for part in stripped.split(","):
        item = part.strip()
        if not item:
            continue
        if "=" not in item:
            raise ValueError(
                f"Invalid hypothesis entry {item!r}; expected JSON object or 'VAR=expr, ...'"
            )
        var, expr = item.split("=", 1)
        var_name = var.strip()
        expr_str = expr.strip()
        if not var_name or not expr_str:
            raise ValueError(f"Invalid hypothesis entry {item!r}")
        mapping[var_name] = expr_str
    return mapping


def _convert_spec_test_domains(raw_domains: Any) -> dict[str, list[int]] | None:
    if raw_domains is None:
        return None
    if isinstance(raw_domains, dict):
        return {str(k): [int(v) for v in vals] for k, vals in raw_domains.items()}
    if isinstance(raw_domains, list):
        collected: dict[str, list[int]] = {}
        for item in raw_domains:
            if not isinstance(item, dict):
                continue
            inp = item.get("input")
            if isinstance(inp, dict):
                for k, v in inp.items():
                    vals = collected.setdefault(str(k), [])
                    iv = int(v)
                    if iv not in vals:
                        vals.append(iv)
        return collected or None
    return None


def _load_spec_file(spec_path: str) -> dict[str, Any]:
    data = json.loads(Path(spec_path).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("Specification file must contain a JSON object")
    return data


def _has_while_loop(stm: Stm) -> bool:
    if isinstance(stm, While):
        return True
    if isinstance(stm, Block):
        return _has_while_loop(stm.body)
    if isinstance(stm, Seq):
        return _has_while_loop(stm.left) or _has_while_loop(stm.right)
    if isinstance(stm, If):
        return _has_while_loop(stm.then_branch) or _has_while_loop(stm.else_branch)
    return False


def _cmd_parse(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    _source, result = parsed

    if args.json:
        _print_json(
            {
                "file": args.file,
                "is_crown_valid": result.is_crown_valid,
                "crown_text": result.crown_text,
                "numbered_crown": result.parse_tree.numbered_crown(),
                "leaf_count": len(result.parse_tree.leaves()),
                "ast": result.ast.to_dict(),
                "parse_tree": result.parse_tree.to_dict(),
            }
        )
        return 0 if result.is_crown_valid else 1

    print(render_ast_text(result))
    print()
    print(f"Крона дерева: {result.crown_text}")
    print(f"Нумерована крона: {result.parse_tree.numbered_crown()}")
    status = "OK" if result.is_crown_valid else "MISMATCH"
    print(f"Синтаксична перевірка крони дерева: {status}")
    return 0 if result.is_crown_valid else 1


def _cmd_check(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    _source, result = parsed

    if not result.is_crown_valid:
        return _emit_error(
            "Parse tree crown mismatch",
            as_json=args.json,
            code="E_CROWN_MISMATCH",
        )

    if args.json:
        _print_json(
            {
                "valid": True,
                "file": args.file,
                "is_crown_valid": result.is_crown_valid,
                "leaf_count": len(result.parse_tree.leaves()),
                "crown_text": result.crown_text,
                "numbered_crown": result.parse_tree.numbered_crown(),
            }
        )
        return 0

    print(
        f"OK: {args.file} "
        f"(leaves={len(result.parse_tree.leaves())}, crown valid)"
    )
    return 0


def _cmd_term(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    source, result = parsed

    try:
        term_res = build_semantic_term(result.ast, source_program=source)
    except SiplError as exc:
        return _emit_error(str(exc), as_json=args.json, code="E_SEMANTIC")

    if args.json or args.format == "json":
        _print_json(term_res.to_dict())
    elif args.format == "unicode":
        print(term_res.format_unicode())
    elif args.format == "latex":
        print(term_res.format_latex())
    else:
        print(term_res.format_derivation_text())
        print(f"LaTeX: {term_res.format_latex()}")
    return 0


def _cmd_eval(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    source, result = parsed

    init_state = _parse_state_arg(args.state, as_json=args.json)
    if init_state is None:
        return 1

    try:
        term_res = build_semantic_term(result.ast, source_program=source)
        eval_res = evaluate_semantic_term(
            term_res.term,
            init_state,
            max_iterations=args.max_iterations,
            max_steps=args.max_steps,
        )
    except (SiplError, ValueError) as exc:
        return _emit_error(str(exc), as_json=args.json, code="E_EVAL")

    if args.json:
        _print_json(eval_res.to_dict())
    else:
        print(eval_res.explanation_text)
    return 0 if eval_res.defined else 1


def _resolve_prove_inputs(args: argparse.Namespace) -> dict[str, Any]:
    spec: dict[str, Any] = {}
    if getattr(args, "spec", None):
        spec = _load_spec_file(args.spec)

    precondition = args.precondition if args.precondition is not None else spec.get("precondition")
    postcondition = (
        args.postcondition if args.postcondition is not None else spec.get("postcondition")
    )

    spec_hyp = spec.get("hypothesis")
    hypothesis: dict[str, str] | None = None
    invariant = args.invariant if args.invariant is not None else spec.get("invariant")

    if getattr(args, "hypothesis", None):
        hypothesis = _parse_hypothesis_arg(args.hypothesis)
    elif isinstance(spec_hyp, dict):
        hypothesis = {str(k): str(v) for k, v in spec_hyp.items()}
    elif isinstance(spec_hyp, str) and invariant is None:
        invariant = spec_hyp

    backward_invariants: list[str] | None = None
    if getattr(args, "backward_invariant", None):
        backward_invariants = list(args.backward_invariant)
    elif isinstance(spec.get("backward_invariants"), list):
        raw_bwd = [str(item) for item in spec["backward_invariants"]]
        if raw_bwd and all("=" in item and "->" not in item for item in raw_bwd):
            backward_invariants = raw_bwd

    test_domains = _convert_spec_test_domains(spec.get("test_domains"))
    return {
        "precondition": precondition,
        "postcondition": postcondition,
        "hypothesis": hypothesis,
        "invariant": invariant,
        "backward_invariants": backward_invariants,
        "test_domains": test_domains,
    }


def _cmd_prove(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    _source, result = parsed

    try:
        inputs = _resolve_prove_inputs(args)
        report = prove_program(
            result.ast,
            precondition=inputs["precondition"],
            postcondition=inputs["postcondition"],
            hypothesis=inputs["hypothesis"],
            invariant=inputs["invariant"],
            backward_invariants=inputs["backward_invariants"],
            mode=args.mode,
            test_domains=inputs["test_domains"],
        )
    except (OSError, ValueError, json.JSONDecodeError, SiplError) as exc:
        return _emit_error(str(exc), as_json=args.json, code="E_PROVE")

    if args.json:
        _print_json(report.to_dict())
    else:
        print(report.explanation_text)

    return 1 if report.status == "disproved" else 0


def _cmd_visualize(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    source, result = parsed

    fmt: str = args.format
    if args.json and not args.output and fmt == "svg":
        fmt = "json"

    rendered: str
    if fmt == "text":
        rendered = render_parse_tree_text(result)
    elif fmt == "json":
        rendered = render_parse_tree_json(result)
    elif fmt == "dot":
        rendered = render_parse_tree_dot(result)
    elif fmt == "svg":
        rendered = render_parse_tree_svg(result)
    elif fmt == "ast-text":
        rendered = render_ast_text(result)
    elif fmt == "ast-json":
        rendered = render_ast_json(result)
    elif fmt == "ast-dot":
        rendered = render_ast_dot(result)
    elif fmt == "ast-svg":
        rendered = render_ast_svg(result)
    elif fmt == "compare-html":
        rendered = render_comparison_html(result)
    elif fmt == "html":
        try:
            sem_term = build_semantic_term(result.ast, source_program=source)
        except SiplSemanticError as exc:
            return _emit_error(str(exc), as_json=args.json, code="E_SEMANTIC")

        eval_res: EvaluationResult | None = None
        if args.state is not None:
            init_state = _parse_state_arg(args.state, as_json=args.json)
            if init_state is None:
                return 1
            eval_res = evaluate_semantic_term(sem_term.term, init_state)

        proof_res: ProofReport | None = None
        should_prove = bool(
            args.spec
            or args.precondition
            or args.postcondition
            or _has_while_loop(result.ast.body)
        )
        if should_prove:
            try:
                inputs = _resolve_prove_inputs(args)
                proof_res = prove_program(
                    result.ast,
                    precondition=inputs["precondition"],
                    postcondition=inputs["postcondition"],
                    hypothesis=inputs["hypothesis"],
                    invariant=inputs["invariant"],
                    backward_invariants=inputs["backward_invariants"],
                    mode=args.mode,
                    test_domains=inputs["test_domains"],
                )
            except (OSError, ValueError, json.JSONDecodeError, SiplError) as exc:
                return _emit_error(str(exc), as_json=args.json, code="E_PROVE")

        rendered = render_pipeline_html(
            result,
            semantic_term=sem_term,
            eval_result=eval_res,
            proof_result=proof_res,
        )
    else:
        return _emit_error(f"Unsupported visualization format: {fmt}", as_json=args.json)

    if args.output:
        out_path = Path(args.output)
        try:
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(rendered, encoding="utf-8")
        except OSError as exc:
            return _emit_error(
                f"Cannot write output '{args.output}': {exc}",
                as_json=args.json,
                code="E_IO",
            )
        if args.json:
            _print_json({"file": args.file, "format": fmt, "output": str(out_path)})
        else:
            print(f"Wrote {fmt} visualization to {out_path}")
        return 0

    if args.json and fmt not in ("json", "ast-json"):
        _print_json({"file": args.file, "format": fmt, "content": rendered})
    else:
        print(rendered)
    return 0


def _cmd_run(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    _source, result = parsed

    init_state = _parse_state_arg(args.state, as_json=args.json)
    if init_state is None:
        return 1

    try:
        exec_res = run_program(result.ast, init_state, max_steps=args.max_steps)
    except (SiplRuntimeError, ValueError) as exc:
        return _emit_error(str(exc), as_json=args.json, code="E_RUNTIME")

    if args.json:
        _print_json(exec_res.to_dict())
    else:
        print(f"Initial state: {exec_res.initial_state.format_course()}")
        if exec_res.is_defined and exec_res.final_state is not None:
            print(f"Final state:   {exec_res.final_state.format_course()}")
            print(f"Steps:         {exec_res.steps_executed}")
        else:
            print(f"Status:        undefined [{exec_res.error_code}] {exec_res.error}")
    return 0 if exec_res.is_defined else 1


def _cmd_trace(args: argparse.Namespace) -> int:
    parsed = _read_and_parse(args.file, strict_bnf=args.strict_bnf, as_json=args.json)
    if parsed is None:
        return 1
    _source, result = parsed

    init_state = _parse_state_arg(args.state, as_json=args.json)
    if init_state is None:
        return 1

    try:
        exec_res = run_program(result.ast, init_state, max_steps=args.max_steps)
    except (SiplRuntimeError, ValueError) as exc:
        return _emit_error(str(exc), as_json=args.json, code="E_RUNTIME")

    if args.json:
        _print_json(
            {
                "is_defined": exec_res.is_defined,
                "initial_state": exec_res.initial_state.to_dict(),
                "final_state": (
                    exec_res.final_state.to_dict() if exec_res.final_state is not None else None
                ),
                "steps_executed": exec_res.steps_executed,
                "error": exec_res.error,
                "error_code": exec_res.error_code,
                "trace": exec_res.trace.to_dict(),
            }
        )
    else:
        print(f"Trace ({len(exec_res.trace.events)} events):")
        for ev in exec_res.trace.events:
            st_str = State(ev.state).format_course()
            details_str = f" {ev.details}" if ev.details else ""
            print(
                f"  [{ev.step:>3}] {ev.event_type:<20} {ev.statement_kind:<8} "
                f"({ev.node_id}){details_str} -> {st_str}"
            )
        if exec_res.is_defined and exec_res.final_state is not None:
            print(f"Final state: {exec_res.final_state.format_course()}")
        else:
            print(f"Status: undefined [{exec_res.error_code}] {exec_res.error}")
    return 0 if exec_res.is_defined else 1


def _add_common_flags(parser: argparse.ArgumentParser, *, is_subparser: bool) -> None:
    default_val: Any = argparse.SUPPRESS if is_subparser else False
    parser.add_argument(
        "--strict-bnf",
        action="store_true",
        default=default_val,
        help="Reject extended operators (div, mod, <=, >=, !=, and, negative literals)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        default=default_val,
        help="Output machine-readable JSON",
    )


def build_parser() -> argparse.ArgumentParser:
    """Construct the CLI argument parser for ``sipl``."""
    parser = argparse.ArgumentParser(
        prog="sipl",
        description=(
            "SIPL Language Toolkit: grammar, AST/parse tree, interpreter, "
            "algebraic semantics, inductive prover, and visualizations."
        ),
        epilog=(
            "Exit codes: 0 on success (for 'prove': proved/partial/unsupported); "
            "1 on syntax/runtime error, undefined evaluation, or 'prove' disproved."
        ),
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    _add_common_flags(parser, is_subparser=False)

    subparsers = parser.add_subparsers(dest="command", required=True, metavar="COMMAND")

    p_parse = subparsers.add_parser("parse", help="Parse SIPL program and print AST & crown")
    p_parse.add_argument("file", help="Path to .sipl source file")
    _add_common_flags(p_parse, is_subparser=True)
    p_parse.set_defaults(func=_cmd_parse)

    p_check = subparsers.add_parser("check", help="Validate syntax and parse-tree crown")
    p_check.add_argument("file", help="Path to .sipl source file")
    _add_common_flags(p_check, is_subparser=True)
    p_check.set_defaults(func=_cmd_check)

    p_term = subparsers.add_parser("term", help="Build algebraic semantic term")
    p_term.add_argument("file", help="Path to .sipl source file")
    p_term.add_argument(
        "--format",
        choices=("unicode", "latex", "derivation", "json"),
        default="derivation",
        help="Output representation format (default: derivation)",
    )
    _add_common_flags(p_term, is_subparser=True)
    p_term.set_defaults(func=_cmd_term)

    p_eval = subparsers.add_parser("eval", help="Evaluate semantic term step-by-step")
    p_eval.add_argument("file", help="Path to .sipl source file")
    p_eval.add_argument("--state", default="", help="Initial state, e.g. 'X=5, Y=2'")
    p_eval.add_argument(
        "--max-iterations",
        type=int,
        default=10_000,
        help="Maximum while-loop iterations (default: 10000)",
    )
    p_eval.add_argument(
        "--max-steps",
        type=int,
        default=100_000,
        help="Maximum algebraic evaluation steps (default: 100000)",
    )
    _add_common_flags(p_eval, is_subparser=True)
    p_eval.set_defaults(func=_cmd_eval)

    p_prove = subparsers.add_parser(
        "prove",
        help="Run automated inductive correctness prover",
    )
    p_prove.add_argument("file", help="Path to .sipl source file")
    p_prove.add_argument("--spec", default=None, help="Path to JSON proof specification file")
    p_prove.add_argument("--precondition", default=None, help="Precondition predicate {P}")
    p_prove.add_argument("--postcondition", default=None, help="Postcondition predicate {Q}")
    p_prove.add_argument(
        "--hypothesis",
        default=None,
        help="User loop hypothesis st_k as JSON object or 'V1=expr1, V2=expr2'",
    )
    p_prove.add_argument("--invariant", default=None, help="Loop invariant predicate")
    p_prove.add_argument(
        "--backward-invariant",
        action="append",
        default=None,
        help="Backward-induction equality invariant (repeatable)",
    )
    p_prove.add_argument(
        "--mode",
        choices=("hybrid", "forward_induction", "backward_induction"),
        default="hybrid",
        help="Proof strategy (default: hybrid)",
    )
    _add_common_flags(p_prove, is_subparser=True)
    p_prove.set_defaults(func=_cmd_prove)

    p_vis = subparsers.add_parser(
        "visualize",
        help="Render Parse Tree, AST, comparison, or 5-panel HTML pipeline",
    )
    p_vis.add_argument("file", help="Path to .sipl source file")
    p_vis.add_argument(
        "--format",
        choices=(
            "text",
            "json",
            "dot",
            "svg",
            "ast-text",
            "ast-json",
            "ast-dot",
            "ast-svg",
            "compare-html",
            "html",
        ),
        default="svg",
        help="Visualization format (default: svg)",
    )
    p_vis.add_argument("--state", default=None, help="Optional initial state for --format html")
    p_vis.add_argument("--spec", default=None, help="Optional spec JSON for --format html")
    p_vis.add_argument(
        "--precondition", default=None, help="Optional precondition for --format html"
    )
    p_vis.add_argument(
        "--postcondition", default=None, help="Optional postcondition for --format html"
    )
    p_vis.add_argument("--invariant", default=None, help="Optional invariant for --format html")
    p_vis.add_argument(
        "--mode",
        choices=("hybrid", "forward_induction", "backward_induction"),
        default="hybrid",
        help="Prover mode for --format html (default: hybrid)",
    )
    p_vis.add_argument("-o", "--output", default=None, help="Write output to file path")
    _add_common_flags(p_vis, is_subparser=True)
    p_vis.set_defaults(func=_cmd_visualize)

    p_run = subparsers.add_parser("run", help="Run AST operational interpreter")
    p_run.add_argument("file", help="Path to .sipl source file")
    p_run.add_argument("--state", default="", help="Initial state, e.g. 'X=5, Y=2'")
    p_run.add_argument(
        "--max-steps",
        type=int,
        default=100_000,
        help="Maximum execution steps (default: 100000)",
    )
    _add_common_flags(p_run, is_subparser=True)
    p_run.set_defaults(func=_cmd_run)

    p_trace = subparsers.add_parser("trace", help="Run AST interpreter and emit trace")
    p_trace.add_argument("file", help="Path to .sipl source file")
    p_trace.add_argument("--state", default="", help="Initial state, e.g. 'X=5, Y=2'")
    p_trace.add_argument(
        "--max-steps",
        type=int,
        default=100_000,
        help="Maximum execution steps (default: 100000)",
    )
    _add_common_flags(p_trace, is_subparser=True)
    p_trace.set_defaults(func=_cmd_trace)

    return parser


def main(argv: list[str] | None = None) -> int:
    """CLI entry point for ``sipl``."""
    _configure_utf8_streams()
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
