"""Algebraic evaluator for semantic terms of A_SIPL."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from sipl.diagnostics import SiplRuntimeError, SourceSpan
from sipl.interpreter.state import State
from sipl.semantics.terms import (
    TFA,
    TFB,
    TFS,
    AssignTerm,
    BlockTerm,
    ConstNumTerm,
    DerefTerm,
    IdTerm,
    IfTerm,
    SemanticTerm,
    SeqTerm,
    SuperposAexpTerm,
    SuperposBoolTerm,
    SuperposCmpTerm,
    WhileTerm,
)


@dataclass(frozen=True, slots=True)
class EvalStep:
    """Single algebraic formula application step during semantic term evaluation."""

    step_index: int
    formula_name: str
    expression_text: str
    input_state: dict[str, int] | None
    output_value: Any
    explanation: str
    state_label: str | None = None
    term_id: str | None = None
    ast_node_id: str | None = None
    span: SourceSpan | None = None

    def to_dict(self) -> dict[str, Any]:
        """Serialize this evaluation step into a JSON-compatible dictionary."""
        return {
            "step_index": self.step_index,
            "formula_name": self.formula_name,
            "expression_text": self.expression_text,
            "input_state": dict(self.input_state) if self.input_state is not None else None,
            "output_value": self.output_value,
            "explanation": self.explanation,
            "state_label": self.state_label,
            "term_id": self.term_id,
            "ast_node_id": self.ast_node_id,
            "span": self.span.to_dict() if self.span is not None else None,
        }


@dataclass(slots=True)
class EvaluationResult:
    """Result of evaluating a ``SemanticTerm`` on an initial ``State``."""

    defined: bool
    initial_state: State
    final_state: State | None
    term: SemanticTerm
    steps: list[EvalStep]
    loop_iterations: list[dict[str, Any]]
    undefined_reason: str | None = None
    error_code: str | None = None
    explanation_text: str = ""
    value: int | bool | None = None

    def to_dict(self) -> dict[str, Any]:
        """Serialize this evaluation result into a JSON-compatible dictionary."""
        data: dict[str, Any] = {
            "defined": self.defined,
            "initial_state": self.initial_state.to_dict(),
            "final_state": self.final_state.to_dict() if self.final_state is not None else None,
            "term": self.term.to_dict(),
            "steps": [step.to_dict() for step in self.steps],
            "loop_iterations": list(self.loop_iterations),
            "undefined_reason": self.undefined_reason,
            "error_code": self.error_code,
            "explanation_text": self.explanation_text,
        }
        if self.value is not None:
            data["value"] = self.value
        return data


def _apply_arith_op(op_name: str, args: list[int], span: SourceSpan | None) -> int:
    if len(args) != 2:
        raise SiplRuntimeError(
            f"Arithmetic operation '{op_name}' expects 2 arguments, got {len(args)}",
            code="E_UNSUPPORTED_OP",
            span=span,
        )
    left, right = args[0], args[1]
    if op_name == "add":
        return left + right
    if op_name == "sub":
        return left - right
    if op_name == "mult":
        return left * right
    if op_name == "div":
        if right == 0:
            raise SiplRuntimeError(
                "Division by zero in 'div'",
                code="E_DIV_ZERO",
                span=span,
            )
        return left // right
    if op_name == "mod":
        if right == 0:
            raise SiplRuntimeError(
                "Modulo by zero in 'mod'",
                code="E_MOD_ZERO",
                span=span,
            )
        return left % right
    raise SiplRuntimeError(
        f"Unsupported arithmetic operation '{op_name}'",
        code="E_UNSUPPORTED_OP",
        span=span,
    )


def _apply_cmp_op(op_name: str, left: int, right: int, span: SourceSpan | None) -> bool:
    if op_name == "eq":
        return left == right
    if op_name == "gr":
        return left > right
    if op_name == "gre":
        return left >= right
    if op_name == "less":
        return left < right
    if op_name == "leq":
        return left <= right
    if op_name == "neq":
        return left != right
    raise SiplRuntimeError(
        f"Unsupported comparison operation '{op_name}'",
        code="E_UNSUPPORTED_OP",
        span=span,
    )


def _apply_bool_op(op_name: str, args: list[bool], span: SourceSpan | None) -> bool:
    if op_name == "neg":
        if len(args) != 1:
            raise SiplRuntimeError(
                f"Boolean operation 'neg' expects 1 argument, got {len(args)}",
                code="E_UNSUPPORTED_OP",
                span=span,
            )
        return not args[0]
    if op_name in ("or", "and"):
        if len(args) != 2:
            raise SiplRuntimeError(
                f"Boolean operation '{op_name}' expects 2 arguments, got {len(args)}",
                code="E_UNSUPPORTED_OP",
                span=span,
            )
        return (args[0] or args[1]) if op_name == "or" else (args[0] and args[1])
    raise SiplRuntimeError(
        f"Unsupported boolean operation '{op_name}'",
        code="E_UNSUPPORTED_OP",
        span=span,
    )


def _bool_str(val: bool) -> str:
    return "true" if val else "false"


class _Evaluator:
    """Recursive evaluator following exact ``A_SIPL`` formulas (p. 14)."""

    def __init__(self, *, max_iterations: int, max_steps: int) -> None:
        self.max_iterations = max_iterations
        self.max_steps = max_steps
        self.steps: list[EvalStep] = []
        self.explanation_lines: list[str] = []
        self.loop_iterations: list[dict[str, Any]] = []
        self._top_state_counter = 0
        self._loop_counter = 0

    def _record_step(
        self,
        formula_name: str,
        expression_text: str,
        input_state: State | None,
        output_value: Any,
        explanation: str,
        *,
        state_label: str | None = None,
        term: SemanticTerm | None = None,
        append_explanation: bool = True,
    ) -> None:
        if len(self.steps) >= self.max_steps:
            raise SiplRuntimeError(
                f"Semantic evaluation exceeded max_steps limit ({self.max_steps})",
                code="E_MAX_STEPS",
                span=term.span if term is not None else None,
            )
        step = EvalStep(
            step_index=len(self.steps) + 1,
            formula_name=formula_name,
            expression_text=expression_text,
            input_state=input_state.to_dict() if input_state is not None else None,
            output_value=output_value,
            explanation=explanation,
            state_label=state_label,
            term_id=term.term_id if term is not None else None,
            ast_node_id=term.ast_node_id if term is not None else None,
            span=term.span if term is not None else None,
        )
        self.steps.append(step)
        if append_explanation:
            self.explanation_lines.append(explanation)

    def _next_top_label(self) -> str:
        label = f"st_{self._top_state_counter}"
        self._top_state_counter += 1
        return label

    def eval_tfa(self, term: TFA, state: State, label: str) -> int:
        if isinstance(term, ConstNumTerm):
            expl = f"{term.format_unicode()}({label}) = {term.value}"
            self._record_step(
                "AF_CONST",
                f"{term.format_unicode()}({label})",
                state,
                term.value,
                expl,
                state_label=label,
                term=term,
                append_explanation=False,
            )
            return term.value

        if isinstance(term, DerefTerm):
            val = state.get(term.var)
            if val is None:
                expl = f"{term.format_unicode()}({label}) = {label}({term.var}) \u2191"
                self._record_step(
                    "AF_DNM",
                    f"{term.format_unicode()}({label})",
                    state,
                    None,
                    expl,
                    state_label=label,
                    term=term,
                    append_explanation=True,
                )
                raise SiplRuntimeError(
                    f"Undefined variable '{term.var}'",
                    code="E_UNDEFINED_VAR",
                    span=term.span,
                )
            expl = f"{term.format_unicode()}({label}) = {label}({term.var}) = {val}"
            self._record_step(
                "AF_DNM",
                f"{term.format_unicode()}({label})",
                state,
                val,
                expl,
                state_label=label,
                term=term,
                append_explanation=False,
            )
            return val

        if isinstance(term, SuperposAexpTerm):
            arg_vals = [self.eval_tfa(arg, state, label) for arg in term.args]
            arg_calls = ", ".join(f"{arg.format_unicode()}({label})" for arg in term.args)
            arg_nums = ", ".join(str(v) for v in arg_vals)
            try:
                res = _apply_arith_op(term.op_name, arg_vals, term.span)
            except SiplRuntimeError:
                expl = (
                    f"{term.format_unicode()}({label}) = "
                    f"{term.op_name}({arg_calls}) = {term.op_name}({arg_nums}) \u2191"
                )
                self._record_step(
                    "AF_S",
                    f"{term.format_unicode()}({label})",
                    state,
                    None,
                    expl,
                    state_label=label,
                    term=term,
                    append_explanation=True,
                )
                raise
            expl = (
                f"{term.format_unicode()}({label}) = "
                f"{term.op_name}({arg_calls}) = {term.op_name}({arg_nums}) = {res}"
            )
            self._record_step(
                "AF_S",
                f"{term.format_unicode()}({label})",
                state,
                res,
                expl,
                state_label=label,
                term=term,
                append_explanation=False,
            )
            return res

        raise SiplRuntimeError(
            f"Unknown TFA term: {type(term).__name__}",
            code="E_INTERNAL",
            span=term.span,
        )

    def eval_tfb(self, term: TFB, state: State, label: str, *, explain: bool = False) -> bool:
        if isinstance(term, SuperposCmpTerm):
            left_val = self.eval_tfa(term.left, state, label)
            right_val = self.eval_tfa(term.right, state, label)
            res = _apply_cmp_op(term.op_name, left_val, right_val, term.span)
            expl = (
                f"{term.format_unicode()}({label}) = "
                f"{term.op_name}({term.left.format_unicode()}({label}), "
                f"{term.right.format_unicode()}({label})) = "
                f"{term.op_name}({left_val}, {right_val}) = {_bool_str(res)}"
            )
            self._record_step(
                "AF_S",
                f"{term.format_unicode()}({label})",
                state,
                res,
                expl,
                state_label=label,
                term=term,
                append_explanation=explain,
            )
            return res

        if isinstance(term, SuperposBoolTerm):
            arg_vals = [self.eval_tfb(arg, state, label, explain=False) for arg in term.args]
            arg_calls = ", ".join(f"{arg.format_unicode()}({label})" for arg in term.args)
            arg_bools = ", ".join(_bool_str(v) for v in arg_vals)
            res = _apply_bool_op(term.op_name, arg_vals, term.span)
            expl = (
                f"{term.format_unicode()}({label}) = "
                f"{term.op_name}({arg_calls}) = {term.op_name}({arg_bools}) = {_bool_str(res)}"
            )
            self._record_step(
                "AF_S",
                f"{term.format_unicode()}({label})",
                state,
                res,
                expl,
                state_label=label,
                term=term,
                append_explanation=explain,
            )
            return res

        raise SiplRuntimeError(
            f"Unknown TFB term: {type(term).__name__}",
            code="E_INTERNAL",
            span=term.span,
        )

    def eval_tfs(
        self,
        term: TFS,
        state: State,
        label: str,
        *,
        sub_ctx: tuple[str, list[int], list[dict[str, Any]]] | None = None,
    ) -> tuple[State, str]:
        if isinstance(term, BlockTerm):
            return self.eval_tfs(term.inner, state, label, sub_ctx=sub_ctx)

        if isinstance(term, IdTerm):
            expl = f"id({label}) = {label} = {state.format_course()}"
            self._record_step(
                "AF_ID",
                f"id({label})",
                state,
                state.to_dict(),
                expl,
                state_label=label,
                term=term,
                append_explanation=True,
            )
            return state, label

        if isinstance(term, AssignTerm):
            val = self.eval_tfa(term.expr, state, label)
            new_state = state.overlay({term.var: val})
            if sub_ctx is not None:
                base_label, sub_counter, sub_records = sub_ctx
                sub_counter[0] += 1
                next_label = f"{base_label}^{sub_counter[0]}"
                sub_records.append({"label": next_label, "state": new_state.to_dict()})
            else:
                next_label = self._next_top_label()

            expl = (
                f"{next_label} = {term.format_unicode()}({label}) = "
                f"{label}\u2207[{term.var} \u21a6 {term.expr.format_unicode()}({label})] = "
                f"{label}\u2207[{term.var} \u21a6 {val}] = {new_state.format_course()}"
            )
            self._record_step(
                "AF_AS",
                f"{term.format_unicode()}({label})",
                state,
                new_state.to_dict(),
                expl,
                state_label=next_label,
                term=term,
                append_explanation=True,
            )
            return new_state, next_label

        if isinstance(term, SeqTerm):
            expl_seq = (
                f"({term.format_unicode()})({label}) = "
                f"({term.right.format_unicode()})(({term.left.format_unicode()})({label}))"
            )
            self._record_step(
                "AF_SEQ",
                f"({term.format_unicode()})({label})",
                state,
                None,
                expl_seq,
                state_label=label,
                term=term,
                append_explanation=True,
            )
            mid_state, mid_label = self.eval_tfs(term.left, state, label, sub_ctx=sub_ctx)
            return self.eval_tfs(term.right, mid_state, mid_label, sub_ctx=sub_ctx)

        if isinstance(term, IfTerm):
            cond_val = self.eval_tfb(term.cond, state, label, explain=True)
            branch_word = "істинна" if cond_val else "хибна"
            branch_term = term.then_term if cond_val else term.else_term
            expl_if = (
                f"{term.format_unicode()}({label}): умова "
                f"{term.cond.format_unicode()}({label}) {branch_word} "
                f"({_bool_str(cond_val)}), виконуємо "
                f"{branch_term.format_unicode()}({label})."
            )
            self._record_step(
                "AF_IF",
                f"{term.format_unicode()}({label})",
                state,
                {"condition": cond_val, "branch": "then" if cond_val else "else"},
                expl_if,
                state_label=label,
                term=term,
                append_explanation=True,
            )
            return self.eval_tfs(branch_term, state, label, sub_ctx=sub_ctx)

        if isinstance(term, WhileTerm):
            self._loop_counter += 1
            is_first_loop = self._loop_counter == 1
            entry_label = label
            curr_state = state
            curr_label = entry_label
            iter_idx = 0

            self.explanation_lines.append(
                f"Застосовуємо {term.format_unicode()} до стану {entry_label} = "
                f"{curr_state.format_course()}:"
            )

            while True:
                cond_val = self.eval_tfb(term.cond, curr_state, curr_label, explain=True)
                if not cond_val:
                    exit_expl = (
                        f"Умова циклу на стані {curr_label} хибна (false); "
                        f"NumItWH(({term.cond.format_unicode()}, "
                        f"{term.body.format_unicode()}), {entry_label}) = {iter_idx}. "
                        f"Результат циклу: {curr_label} = {curr_state.format_course()}."
                    )
                    self._record_step(
                        "AF_WH",
                        f"{term.format_unicode()}({entry_label})",
                        curr_state,
                        {
                            "final_state": curr_state.to_dict(),
                            "NumItWH": iter_idx,
                        },
                        exit_expl,
                        state_label=curr_label,
                        term=term,
                        append_explanation=True,
                    )
                    return curr_state, curr_label

                if iter_idx >= self.max_iterations:
                    fail_expl = (
                        f"Перевищено ліміт ітерацій циклу ({self.max_iterations}): "
                        f"{term.format_unicode()}({entry_label}) \u2191."
                    )
                    self._record_step(
                        "AF_WH",
                        f"{term.format_unicode()}({entry_label})",
                        curr_state,
                        None,
                        fail_expl,
                        state_label=curr_label,
                        term=term,
                        append_explanation=True,
                    )
                    raise SiplRuntimeError(
                        f"While loop exceeded max_iterations limit ({self.max_iterations})",
                        code="E_MAX_ITERATIONS",
                        span=term.span,
                    )

                iter_idx += 1
                self.explanation_lines.append(
                    f"Умова циклу істинна (true), виконуємо ітерацію {iter_idx} "
                    f"зі стану {curr_label}:"
                )

                sub_counter = [0]
                loop_sub_records: list[dict[str, Any]] = []
                iter_sub_ctx = (curr_label, sub_counter, loop_sub_records)

                body_state, _ = self.eval_tfs(
                    term.body, curr_state, curr_label, sub_ctx=iter_sub_ctx
                )
                next_label = (
                    f"st_{iter_idx}"
                    if is_first_loop
                    else f"st_L{self._loop_counter}_{iter_idx}"
                )
                if loop_sub_records:
                    last_sub = loop_sub_records[-1]["label"]
                    self.explanation_lines.append(
                        f"Стан після ітерації {iter_idx}: {next_label} = "
                        f"{last_sub} = {body_state.format_course()}."
                    )
                else:
                    self.explanation_lines.append(
                        f"Стан після ітерації {iter_idx}: {next_label} = "
                        f"{body_state.format_course()}."
                    )

                self.loop_iterations.append(
                    {
                        "loop_term_id": term.term_id,
                        "iteration": iter_idx,
                        "input_state_label": curr_label,
                        "input_state": curr_state.to_dict(),
                        "condition_term": term.cond.format_unicode(),
                        "condition_value": True,
                        "intermediate_states": loop_sub_records,
                        "output_state_label": next_label,
                        "output_state": body_state.to_dict(),
                    }
                )
                curr_state = body_state
                curr_label = next_label

        raise SiplRuntimeError(
            f"Unknown TFS term: {type(term).__name__}",
            code="E_INTERNAL",
            span=term.span,
        )


def eval_tfa(term: TFA, state: State) -> int:
    """Evaluate a nominative arithmetic function term ``TFA`` under ``state``."""
    evaluator = _Evaluator(max_iterations=10_000, max_steps=100_000)
    return evaluator.eval_tfa(term, state, "st")


def eval_tfb(term: TFB, state: State) -> bool:
    """Evaluate a nominative predicate term ``TFB`` under ``state``."""
    evaluator = _Evaluator(max_iterations=10_000, max_steps=100_000)
    return evaluator.eval_tfb(term, state, "st")


def evaluate_semantic_term(
    term: SemanticTerm,
    initial_state: State,
    *,
    max_iterations: int = 10_000,
    max_steps: int = 100_000,
) -> EvaluationResult:
    """Evaluate a ``SemanticTerm`` (``TFS``, ``TFA``, or ``TFB``) on ``initial_state``.

    Follows the algebraic semantics of ``A_SIPL`` (``AF_S``, ``AF_AS``, ``AF_SEQ``,
    ``AF_IF``, ``AF_WH``, ``AF_DNM``, ``AF_ID``) and produces Ukrainian step-by-step
    explanations along with intermediate state traces.
    """
    if max_iterations < 0:
        raise ValueError(f"max_iterations must be non-negative, got {max_iterations}")
    if max_steps < 0:
        raise ValueError(f"max_steps must be non-negative, got {max_steps}")

    evaluator = _Evaluator(max_iterations=max_iterations, max_steps=max_steps)
    evaluator.explanation_lines.append(
        f"Обчислення терму {term.format_unicode()} на початковому стані "
        f"st = {initial_state.format_course()}."
    )

    try:
        if isinstance(term, TFS):
            final_state, final_label = evaluator.eval_tfs(term, initial_state, "st")
            evaluator.explanation_lines.append(
                f"Результат обчислення: {term.format_unicode()}(st)\u2193 = "
                f"{final_label} = {final_state.format_course()}."
            )
            return EvaluationResult(
                defined=True,
                initial_state=initial_state,
                final_state=final_state,
                term=term,
                steps=evaluator.steps,
                loop_iterations=evaluator.loop_iterations,
                explanation_text="\n".join(evaluator.explanation_lines),
            )
        if isinstance(term, TFA):
            val_int = evaluator.eval_tfa(term, initial_state, "st")
            evaluator.explanation_lines.append(
                f"Результат обчислення: {term.format_unicode()}(st)\u2193 = {val_int}."
            )
            return EvaluationResult(
                defined=True,
                initial_state=initial_state,
                final_state=initial_state,
                term=term,
                steps=evaluator.steps,
                loop_iterations=evaluator.loop_iterations,
                explanation_text="\n".join(evaluator.explanation_lines),
                value=val_int,
            )
        if isinstance(term, TFB):
            val_bool = evaluator.eval_tfb(term, initial_state, "st", explain=True)
            evaluator.explanation_lines.append(
                f"Результат обчислення: {term.format_unicode()}(st)\u2193 = {_bool_str(val_bool)}."
            )
            return EvaluationResult(
                defined=True,
                initial_state=initial_state,
                final_state=initial_state,
                term=term,
                steps=evaluator.steps,
                loop_iterations=evaluator.loop_iterations,
                explanation_text="\n".join(evaluator.explanation_lines),
                value=val_bool,
            )
        raise SiplRuntimeError(
            f"Unsupported semantic term type: {type(term).__name__}",
            code="E_INTERNAL",
            span=term.span,
        )
    except SiplRuntimeError as exc:
        evaluator.explanation_lines.append(
            f"Функція невизначена на стані st: {term.format_unicode()}(st)\u2191 ({exc})."
        )
        return EvaluationResult(
            defined=False,
            initial_state=initial_state,
            final_state=None,
            term=term,
            steps=evaluator.steps,
            loop_iterations=evaluator.loop_iterations,
            undefined_reason=str(exc),
            error_code=exc.code,
            explanation_text="\n".join(evaluator.explanation_lines),
        )
