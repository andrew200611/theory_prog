"""AST interpreter and event trace engine for SIPL."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from sipl.ast import (
    Aexp,
    Assign,
    Bexp,
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
    Skip,
    Stm,
    Variable,
    While,
)
from sipl.diagnostics import SiplRuntimeError, SourceSpan
from sipl.interpreter.state import State

_EVENT_TYPES = frozenset(
    {
        "BeforeStatement",
        "AfterStatement",
        "VariableChanged",
        "ConditionEvaluated",
        "ProgramFinished",
        "ProgramUndefined",
    }
)


@dataclass(frozen=True, slots=True)
class TraceEvent:
    """Single execution trace event emitted by the SIPL interpreter."""

    step: int
    event_type: str
    node_id: str | None
    span: SourceSpan | None
    statement_kind: str | None
    state: dict[str, int]
    details: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        """Serialize this trace event into a JSON-compatible dictionary."""
        return {
            "step": self.step,
            "event_type": self.event_type,
            "node_id": self.node_id,
            "span": self.span.to_dict() if self.span is not None else None,
            "statement_kind": self.statement_kind,
            "state": dict(self.state),
            "details": dict(self.details),
        }


@dataclass(slots=True)
class ExecutionTrace:
    """Ordered sequence of ``TraceEvent`` entries produced during program execution."""

    events: list[TraceEvent]
    steps_executed: int

    def to_dict(self) -> dict[str, Any]:
        """Serialize the full execution trace into a JSON-compatible dictionary."""
        return {
            "steps_executed": self.steps_executed,
            "events": [event.to_dict() for event in self.events],
        }


@dataclass(slots=True)
class ExecutionResult:
    """Result of executing a SIPL ``Program`` on an initial ``State``."""

    status: str
    initial_state: State
    final_state: State | None
    trace: ExecutionTrace
    steps_executed: int
    error: str | None = None
    error_code: str | None = None
    error_span: SourceSpan | None = None

    @property
    def is_defined(self) -> bool:
        """Return ``True`` iff execution terminated normally (``fs(st)↓``)."""
        return self.status == "finished"

    def to_dict(self) -> dict[str, Any]:
        """Serialize execution result into a JSON-compatible dictionary."""
        return {
            "status": self.status,
            "is_defined": self.is_defined,
            "initial_state": self.initial_state.to_dict(),
            "final_state": self.final_state.to_dict() if self.final_state is not None else None,
            "steps_executed": self.steps_executed,
            "error": self.error,
            "error_code": self.error_code,
            "error_span": self.error_span.to_dict() if self.error_span is not None else None,
            "trace": self.trace.to_dict(),
        }


def eval_aexp(expr: Aexp, state: State) -> int:
    """Evaluate a SIPL arithmetic expression ``Aexp`` under ``state``."""
    if isinstance(expr, Number):
        return expr.value
    if isinstance(expr, Variable):
        val = state.get(expr.name)
        if val is None:
            raise SiplRuntimeError(
                f"Undefined variable '{expr.name}'",
                code="E_UNDEFINED_VAR",
                span=expr.span,
            )
        return val
    if isinstance(expr, ParenAexp):
        return eval_aexp(expr.expr, state)
    if isinstance(expr, BinaryAexp):
        left = eval_aexp(expr.left, state)
        right = eval_aexp(expr.right, state)
        if expr.op == "+":
            return left + right
        if expr.op == "-":
            return left - right
        if expr.op == "*":
            return left * right
        if expr.op == "div":
            if right == 0:
                raise SiplRuntimeError(
                    "Division by zero in 'div'",
                    code="E_DIV_ZERO",
                    span=expr.span,
                )
            return left // right
        if expr.op == "mod":
            if right == 0:
                raise SiplRuntimeError(
                    "Modulo by zero in 'mod'",
                    code="E_MOD_ZERO",
                    span=expr.span,
                )
            return left % right
        raise SiplRuntimeError(
            f"Unsupported arithmetic operator '{expr.op}'",
            code="E_UNSUPPORTED_OP",
            span=expr.span,
        )
    raise SiplRuntimeError(
        f"Unknown Aexp node: {type(expr).__name__}",
        code="E_INTERNAL",
        span=expr.span,
    )


def eval_bexp(cond: Bexp, state: State) -> bool:
    """Evaluate a SIPL boolean condition ``Bexp`` under ``state``."""
    if isinstance(cond, CompareBexp):
        left = eval_aexp(cond.left, state)
        right = eval_aexp(cond.right, state)
        if cond.op == "=":
            return left == right
        if cond.op == ">":
            return left > right
        if cond.op == ">=":
            return left >= right
        if cond.op == "<":
            return left < right
        if cond.op == "<=":
            return left <= right
        if cond.op == "!=":
            return left != right
        raise SiplRuntimeError(
            f"Unsupported comparison operator '{cond.op}'",
            code="E_UNSUPPORTED_OP",
            span=cond.span,
        )
    if isinstance(cond, NotBexp):
        return not eval_bexp(cond.operand, state)
    if isinstance(cond, ParenBexp):
        return eval_bexp(cond.cond, state)
    if isinstance(cond, BinaryBexp):
        left = eval_bexp(cond.left, state)
        right = eval_bexp(cond.right, state)
        if cond.op == "or":
            return left or right
        if cond.op == "and":
            return left and right
        raise SiplRuntimeError(
            f"Unsupported boolean operator '{cond.op}'",
            code="E_UNSUPPORTED_OP",
            span=cond.span,
        )
    raise SiplRuntimeError(
        f"Unknown Bexp node: {type(cond).__name__}",
        code="E_INTERNAL",
        span=cond.span,
    )


class _Interpreter:
    """Internal AST interpreter tracking execution steps and emitting trace events."""

    def __init__(self, initial_state: State, *, max_steps: int) -> None:
        self.state = initial_state
        self.max_steps = max_steps
        self.steps = 0
        self.events: list[TraceEvent] = []

    def _emit(
        self,
        event_type: str,
        node_id: str | None,
        span: SourceSpan | None,
        statement_kind: str | None,
        details: dict[str, Any] | None = None,
    ) -> None:
        assert event_type in _EVENT_TYPES
        self.events.append(
            TraceEvent(
                step=self.steps,
                event_type=event_type,
                node_id=node_id,
                span=span,
                statement_kind=statement_kind,
                state=self.state.to_dict(),
                details=details or {},
            )
        )

    def _consume_step(self, span: SourceSpan) -> None:
        if self.steps >= self.max_steps:
            raise SiplRuntimeError(
                f"Execution exceeded max_steps limit ({self.max_steps})",
                code="E_MAX_STEPS",
                span=span,
            )
        self.steps += 1

    def exec_stm(self, stm: Stm) -> None:
        kind = stm.__class__.__name__
        self._emit("BeforeStatement", stm.node_id, stm.span, kind)

        if isinstance(stm, Skip):
            self._consume_step(stm.span)
        elif isinstance(stm, Assign):
            self._consume_step(stm.span)
            new_val = eval_aexp(stm.expr, self.state)
            old_val = self.state.get(stm.var)
            self.state = self.state.overlay({stm.var: new_val})
            self._emit(
                "VariableChanged",
                stm.node_id,
                stm.span,
                kind,
                {"var": stm.var, "old": old_val, "new": new_val},
            )
        elif isinstance(stm, Seq):
            self.exec_stm(stm.left)
            self.exec_stm(stm.right)
        elif isinstance(stm, Block):
            self.exec_stm(stm.body)
        elif isinstance(stm, If):
            self._consume_step(stm.span)
            cond_val = eval_bexp(stm.cond, self.state)
            self._emit(
                "ConditionEvaluated",
                stm.cond.node_id,
                stm.cond.span,
                kind,
                {"result": cond_val, "parent_node_id": stm.node_id},
            )
            if cond_val:
                self.exec_stm(stm.then_branch)
            else:
                self.exec_stm(stm.else_branch)
        elif isinstance(stm, While):
            while True:
                self._consume_step(stm.span)
                cond_val = eval_bexp(stm.cond, self.state)
                self._emit(
                    "ConditionEvaluated",
                    stm.cond.node_id,
                    stm.cond.span,
                    kind,
                    {"result": cond_val, "parent_node_id": stm.node_id},
                )
                if not cond_val:
                    break
                self.exec_stm(stm.body)
        else:
            raise SiplRuntimeError(
                f"Unknown statement node: {kind}",
                code="E_INTERNAL",
                span=stm.span,
            )

        self._emit("AfterStatement", stm.node_id, stm.span, kind)


def run_program(
    program: Program,
    initial_state: State,
    *,
    max_steps: int = 100_000,
) -> ExecutionResult:
    """Execute a parsed SIPL ``Program`` from ``initial_state``.

    Returns an ``ExecutionResult`` with ``status="finished"`` and the resulting
    ``State``, or ``status="undefined"`` when execution encounters an undefined
    variable, division/modulo by zero, or exceeds ``max_steps``.
    """
    if max_steps < 0:
        raise ValueError(f"max_steps must be non-negative, got {max_steps}")

    interp = _Interpreter(initial_state, max_steps=max_steps)
    try:
        interp.exec_stm(program.body)
    except SiplRuntimeError as exc:
        interp._emit(
            "ProgramUndefined",
            program.node_id,
            exc.span or program.span,
            "Program",
            {"reason": str(exc), "code": exc.code},
        )
        trace = ExecutionTrace(events=interp.events, steps_executed=interp.steps)
        return ExecutionResult(
            status="undefined",
            initial_state=initial_state,
            final_state=None,
            trace=trace,
            steps_executed=interp.steps,
            error=str(exc),
            error_code=exc.code,
            error_span=exc.span,
        )

    interp._emit(
        "ProgramFinished",
        program.node_id,
        program.span,
        "Program",
        {"final_state": interp.state.to_dict()},
    )
    trace = ExecutionTrace(events=interp.events, steps_executed=interp.steps)
    return ExecutionResult(
        status="finished",
        initial_state=initial_state,
        final_state=interp.state,
        trace=trace,
        steps_executed=interp.steps,
    )
