"""Automated inductive correctness prover for SIPL programs."""

from __future__ import annotations

import itertools
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Any

from sipl.ast import Assign, Bexp, Block, If, Program, Seq, Skip, Stm, While
from sipl.diagnostics import SiplSemanticError
from sipl.interpreter.runtime import run_program
from sipl.interpreter.state import State
from sipl.semantics.symbolic import (
    SymAdd,
    SymAnd,
    SymBool,
    SymBoolConst,
    SymCmp,
    SymConst,
    SymDiv,
    SymExpr,
    SymFact,
    SymIf,
    SymMod,
    SymMul,
    SymNot,
    SymPow,
    SymState,
    SymSub,
    SymVar,
    aexp_to_sym,
    bexp_to_sym,
    eval_sym_bool,
    eval_sym_expr,
    parse_sym_bool,
    parse_sym_expr,
    simplify,
    simplify_bool,
    subst,
    subst_bool,
    sym_equals,
)


@dataclass(slots=True)
class ProofStep:
    """Single verification obligation step inside a ``ProofReport``."""

    title: str
    status: str
    formula: str
    details: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "title": self.title,
            "status": self.status,
            "formula": self.formula,
            "details": self.details,
        }


@dataclass(slots=True)
class Counterexample:
    """Concrete failing input/trace discovered during verification."""

    initial_state: dict[str, int]
    iteration: int | None
    expected: Any
    actual: Any
    reason: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "initial_state": dict(self.initial_state),
            "iteration": self.iteration,
            "expected": self.expected,
            "actual": self.actual,
            "reason": self.reason,
        }


@dataclass(slots=True)
class ProofReport:
    """Complete inductive proof report (Practice 3 format)."""

    program_summary: str
    status: str
    mode: str
    initial_symbolic_state: dict[str, str]
    pre_loop_state: dict[str, str]
    loop_condition: str
    hypothesis_k: dict[str, str]
    hypothesis_source: str
    base_case: ProofStep
    inductive_step: ProofStep
    termination_and_exit: ProofStep
    backward_induction: ProofStep | None
    counterexamples: list[Counterexample] = field(default_factory=list)
    limitations: list[str] = field(default_factory=list)
    explanation_text: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "program_summary": self.program_summary,
            "status": self.status,
            "mode": self.mode,
            "initial_symbolic_state": dict(self.initial_symbolic_state),
            "pre_loop_state": dict(self.pre_loop_state),
            "loop_condition": self.loop_condition,
            "hypothesis_k": dict(self.hypothesis_k),
            "hypothesis_source": self.hypothesis_source,
            "base_case": self.base_case.to_dict(),
            "inductive_step": self.inductive_step.to_dict(),
            "termination_and_exit": self.termination_and_exit.to_dict(),
            "backward_induction": (
                self.backward_induction.to_dict() if self.backward_induction is not None else None
            ),
            "counterexamples": [cx.to_dict() for cx in self.counterexamples],
            "limitations": list(self.limitations),
            "explanation_text": self.explanation_text,
        }


def _flatten_stms(stm: Stm) -> list[Stm]:
    if isinstance(stm, Skip):
        return []
    if isinstance(stm, Block):
        return _flatten_stms(stm.body)
    if isinstance(stm, Seq):
        return _flatten_stms(stm.left) + _flatten_stms(stm.right)
    return [stm]


def _collect_vars_stm(stm: Stm) -> list[str]:
    ordered: list[str] = []
    seen: set[str] = set()

    def add(name: str) -> None:
        if name not in seen:
            seen.add(name)
            ordered.append(name)

    def visit_aexp(expr: Any) -> None:
        sym = aexp_to_sym(expr)
        for v in sorted(sym.free_vars()):
            add(v)

    def visit_bexp(cond: Bexp) -> None:
        sym = bexp_to_sym(cond)
        for v in sorted(sym.free_vars()):
            add(v)

    def visit(node: Stm) -> None:
        if isinstance(node, Skip):
            return
        if isinstance(node, Assign):
            visit_aexp(node.expr)
            add(node.var)
        elif isinstance(node, Block):
            visit(node.body)
        elif isinstance(node, Seq):
            visit(node.left)
            visit(node.right)
        elif isinstance(node, If):
            visit_bexp(node.cond)
            visit(node.then_branch)
            visit(node.else_branch)
        elif isinstance(node, While):
            visit_bexp(node.cond)
            visit(node.body)

    visit(stm)
    return ordered


def _has_branch_or_loop(stm: Stm) -> bool:
    for item in _flatten_stms(stm):
        if isinstance(item, (If, While)):
            return True
    return False


@dataclass(slots=True)
class _ProgramStructure:
    all_vars: list[str]
    input_vars: list[str]
    init_symbols: dict[str, str]
    prologue: list[Assign]
    while_node: While | None
    epilogue: list[Assign]
    limitations: list[str]
    is_supported_single_loop: bool
    has_unsupported_control_flow: bool


def _analyze_structure(program: Program) -> _ProgramStructure:
    all_vars = _collect_vars_stm(program.body)
    top_stms = _flatten_stms(program.body)
    limitations: list[str] = []

    while_indices = [i for i, s in enumerate(top_stms) if isinstance(s, While)]
    has_unsupported = False

    if len(while_indices) > 1:
        limitations.append(
            "Програма містить кілька послідовних циклів while; "
            "автоматичне індуктивне доведення підтримує лише один зовнішній цикл."
        )
        has_unsupported = True

    prologue: list[Assign] = []
    epilogue: list[Assign] = []
    while_node: While | None = None

    if while_indices:
        idx = while_indices[0]
        while_candidate = top_stms[idx]
        if isinstance(while_candidate, While):
            while_node = while_candidate
        for s in top_stms[:idx]:
            if isinstance(s, Assign):
                prologue.append(s)
            else:
                limitations.append(
                    f"Пролог перед циклом містить не-присвоювання ({type(s).__name__}); "
                    "автоматичний синтез st₀ не застосовний."
                )
                has_unsupported = True
        for s in top_stms[idx + 1 :]:
            if isinstance(s, Assign):
                epilogue.append(s)
            elif not isinstance(s, While):
                limitations.append(
                    f"Епілог після циклу містить не-присвоювання ({type(s).__name__})."
                )
                has_unsupported = True
        assert while_node is not None
        if _has_branch_or_loop(while_node.body):
            limitations.append(
                "Тіло циклу містить розгалуження (if) або вкладений цикл; "
                "автоматичний синтез замкненої форми st_k неможливий."
            )
            has_unsupported = True
    else:
        for s in top_stms:
            if isinstance(s, Assign):
                prologue.append(s)
            else:
                limitations.append(
                    f"Програма без циклу містить {type(s).__name__}; "
                    "автоматичне індуктивне доведення орієнтоване на цикли while."
                )
                has_unsupported = True

    assigned_in_prologue: set[str] = set()
    input_vars: list[str] = []

    def add_input(v: str) -> None:
        if v not in input_vars:
            input_vars.append(v)

    for s in prologue:
        for v in sorted(aexp_to_sym(s.expr).free_vars()):
            if v not in assigned_in_prologue:
                add_input(v)
        assigned_in_prologue.add(s.var)

    for s in top_stms[while_indices[0] :] if while_indices else []:
        for v in _collect_vars_stm(s):
            if v not in assigned_in_prologue:
                add_input(v)

    init_symbols: dict[str, str] = {}
    used_syms = set(all_vars) | {"k"}
    for v in input_vars:
        cand = v.lower()
        if cand != v and cand not in used_syms:
            init_symbols[v] = cand
            used_syms.add(cand)
        else:
            fallback = f"{v.lower()}0" if cand not in used_syms else f"{v}_0"
            while fallback in used_syms:
                fallback = f"{fallback}_"
            init_symbols[v] = fallback
            used_syms.add(fallback)

    is_single_loop = while_node is not None and not has_unsupported
    return _ProgramStructure(
        all_vars=all_vars,
        input_vars=input_vars,
        init_symbols=init_symbols,
        prologue=prologue,
        while_node=while_node,
        epilogue=epilogue,
        limitations=limitations,
        is_supported_single_loop=is_single_loop,
        has_unsupported_control_flow=has_unsupported,
    )


def _compute_pre_loop_state(
    struct: _ProgramStructure,
) -> tuple[dict[str, SymExpr], dict[str, SymExpr]]:
    init_state: dict[str, SymExpr] = {
        v: SymVar(sym_name) for v, sym_name in struct.init_symbols.items()
    }
    st_0: dict[str, SymExpr] = dict(init_state)
    for assign in struct.prologue:
        expr_sym = aexp_to_sym(assign.expr)
        st_0[assign.var] = simplify(subst(expr_sym, st_0))
    for v in struct.all_vars:
        if v not in st_0:
            st_0[v] = SymVar(struct.init_symbols.get(v, v.lower()))
    return init_state, st_0


def _compute_loop_step_map(body: Stm, variables: list[str]) -> dict[str, SymExpr]:
    """Compute simultaneous transition ``V_{k+1} = F_V(st_k)`` for a straight-line body."""
    cur: dict[str, SymExpr] = {v: SymVar(v) for v in variables}
    for stm in _flatten_stms(body):
        if isinstance(stm, Assign):
            rhs = simplify(subst(aexp_to_sym(stm.expr), cur))
            cur[stm.var] = rhs
    return cur


def _poly_coeffs_in_var(expr: SymExpr, var: str, max_deg: int = 3) -> list[SymExpr] | None:
    """Return ``[c_0, ..., c_d]`` if ``expr`` is a polynomial in ``var`` (deg <= ``max_deg``)."""
    s = simplify(expr)

    def rec(node: SymExpr) -> list[SymExpr] | None:
        if var not in node.free_vars():
            return [node]
        if isinstance(node, SymVar):
            return [SymConst(0), SymConst(1)]
        if isinstance(node, SymAdd):
            p = rec(node.left)
            q = rec(node.right)
            if p is None or q is None:
                return None
            n = max(len(p), len(q))
            return [
                simplify(
                    SymAdd(
                        p[i] if i < len(p) else SymConst(0),
                        q[i] if i < len(q) else SymConst(0),
                    )
                )
                for i in range(n)
            ]
        if isinstance(node, SymSub):
            p = rec(node.left)
            q = rec(node.right)
            if p is None or q is None:
                return None
            n = max(len(p), len(q))
            return [
                simplify(
                    SymSub(
                        p[i] if i < len(p) else SymConst(0),
                        q[i] if i < len(q) else SymConst(0),
                    )
                )
                for i in range(n)
            ]
        if isinstance(node, SymMul):
            p = rec(node.left)
            q = rec(node.right)
            if p is None or q is None:
                return None
            if (len(p) - 1) + (len(q) - 1) > max_deg:
                return None
            res: list[SymExpr] = [SymConst(0)] * (len(p) + len(q) - 1)
            for i, ci in enumerate(p):
                for j, cj in enumerate(q):
                    res[i + j] = simplify(SymAdd(res[i + j], SymMul(ci, cj)))
            return res
        if (
            isinstance(node, SymPow)
            and isinstance(node.exp, SymConst)
            and 0 <= node.exp.value <= max_deg
        ):
            base_p = rec(node.base)
            if base_p is None:
                return None
            acc: list[SymExpr] = [SymConst(1)]
            for _ in range(node.exp.value):
                if (len(acc) - 1) + (len(base_p) - 1) > max_deg:
                    return None
                nxt: list[SymExpr] = [SymConst(0)] * (len(acc) + len(base_p) - 1)
                for i, ci in enumerate(acc):
                    for j, cj in enumerate(base_p):
                        nxt[i + j] = simplify(SymAdd(nxt[i + j], SymMul(ci, cj)))
                acc = nxt
            return acc
        return None

    coeffs = rec(s)
    if coeffs is None:
        return None
    while len(coeffs) > 1 and coeffs[-1] == SymConst(0):
        coeffs.pop()
    return coeffs


def _extract_linear_multiplier(expr: SymExpr, var: str) -> SymExpr | None:
    """If ``expr == var * m`` where ``m`` does not depend on ``var``, return ``m``."""
    coeffs = _poly_coeffs_in_var(expr, var, max_deg=1)
    if coeffs is not None and len(coeffs) == 2 and coeffs[0] == SymConst(0):
        return coeffs[1]
    s = simplify(expr)
    if isinstance(s, SymMul):
        if s.left == SymVar(var) and var not in s.right.free_vars():
            return s.right
        if s.right == SymVar(var) and var not in s.left.free_vars():
            return s.left
        left_m = _extract_linear_multiplier(s.left, var)
        if left_m is not None and var not in s.right.free_vars():
            return simplify(SymMul(left_m, s.right))
        right_m = _extract_linear_multiplier(s.right, var)
        if right_m is not None and var not in s.left.free_vars():
            return simplify(SymMul(s.left, right_m))
    return None


def _extract_geometric_term(expr: SymExpr, var: str) -> tuple[SymExpr, int] | None:
    """If ``expr == coeff * base^var`` with integer ``base >= 2`` and ``var`` not in ``coeff``."""
    s = simplify(expr)
    if isinstance(s, SymPow) and isinstance(s.base, SymConst) and s.base.value >= 2:
        if s.exp == SymVar(var):
            return SymConst(1), s.base.value
    if isinstance(s, SymMul):
        if var not in s.left.free_vars():
            sub = _extract_geometric_term(s.right, var)
            if sub is not None:
                return simplify(SymMul(s.left, sub[0])), sub[1]
        if var not in s.right.free_vars():
            sub = _extract_geometric_term(s.left, var)
            if sub is not None:
                return simplify(SymMul(s.right, sub[0])), sub[1]
    return None


def _sum_poly_0_to_k_minus_1(coeffs: list[SymExpr], k_var: SymExpr) -> SymExpr:
    """Compute closed form for ``sum_{j=0}^{k-1} (c_0 + c_1 j + c_2 j^2)``."""
    res: SymExpr = SymConst(0)
    if len(coeffs) >= 1 and coeffs[0] != SymConst(0):
        res = SymAdd(res, SymMul(coeffs[0], k_var))
    if len(coeffs) >= 2 and coeffs[1] != SymConst(0):
        c1 = coeffs[1]
        k_km1 = SymMul(k_var, SymSub(k_var, SymConst(1)))
        if isinstance(c1, SymConst) and c1.value % 2 == 0:
            term: SymExpr = SymMul(SymConst(c1.value // 2), k_km1)
        else:
            term = SymDiv(SymMul(c1, k_km1), SymConst(2))
        res = SymAdd(res, term)
    if len(coeffs) >= 3 and coeffs[2] != SymConst(0):
        c2 = coeffs[2]
        numer = SymMul(
            SymMul(SymSub(k_var, SymConst(1)), k_var),
            SymSub(SymMul(SymConst(2), k_var), SymConst(1)),
        )
        if isinstance(c2, SymConst) and c2.value % 6 == 0:
            term2: SymExpr = SymMul(SymConst(c2.value // 6), numer)
        else:
            term2 = SymDiv(SymMul(c2, numer), SymConst(6))
        res = SymAdd(res, term2)
    return simplify(res)


def synthesize_loop_hypothesis(
    program: Program,
    precondition: str | None = None,
) -> tuple[dict[str, SymExpr], dict[str, SymExpr], list[str]]:
    """Synthesize ``(st_0, st_k, limitations)`` for a SIPL program with a ``while`` loop.

    Inspects prologue assignments to construct ``st_0`` in lowercase symbolic input
    variables, then analyzes sequential loop-body assignments to solve closed-form
    state expressions ``st_k`` as a function of iteration count ``k``.
    """
    _ = precondition
    struct = _analyze_structure(program)
    _, st_0 = _compute_pre_loop_state(struct)
    limitations = list(struct.limitations)

    if not struct.is_supported_single_loop or struct.while_node is None:
        return st_0, dict(st_0), limitations

    step_map = _compute_loop_step_map(struct.while_node.body, struct.all_vars)
    k_var = SymVar("k")
    solved: dict[str, SymExpr] = {}
    invariants: set[str] = set()

    for v in struct.all_vars:
        if sym_equals(step_map[v], SymVar(v)):
            solved[v] = st_0[v]
            invariants.add(v)

    for _ in range(len(struct.all_vars) + 1):
        progress = False
        for v in struct.all_vars:
            if v in solved:
                continue
            rhs = step_map[v]

            delta = simplify(SymSub(rhs, SymVar(v)))
            if delta.free_vars() <= invariants:
                delta_0 = simplify(subst(delta, solved))
                solved[v] = simplify(SymAdd(st_0[v], SymMul(k_var, delta_0)))
                progress = True
                continue

            mult = _extract_linear_multiplier(rhs, v)
            if mult is not None and mult.free_vars() <= invariants:
                m_0 = simplify(subst(mult, solved))
                solved[v] = simplify(SymMul(st_0[v], SymPow(m_0, k_var)))
                progress = True
                continue

            if v not in delta.free_vars() and delta.free_vars() <= set(solved.keys()):
                g_k = simplify(subst(delta, solved))
                coeffs = _poly_coeffs_in_var(g_k, "k", max_deg=2)
                if coeffs is not None:
                    closed_delta = _sum_poly_0_to_k_minus_1(coeffs, k_var)
                    solved[v] = simplify(SymAdd(st_0[v], closed_delta))
                    progress = True
                    continue
                geom = _extract_geometric_term(g_k, "k")
                if geom is not None:
                    c_expr, base_int = geom
                    if base_int == 2:
                        gsum: SymExpr = SymMul(
                            c_expr, SymSub(SymPow(SymConst(2), k_var), SymConst(1))
                        )
                    else:
                        gsum = SymDiv(
                            SymMul(c_expr, SymSub(SymPow(SymConst(base_int), k_var), SymConst(1))),
                            SymConst(base_int - 1),
                        )
                    solved[v] = simplify(SymAdd(st_0[v], gsum))
                    progress = True
                    continue

            if (
                mult is not None
                and v not in mult.free_vars()
                and mult.free_vars() <= set(solved.keys())
            ):
                f_k = simplify(subst(mult, solved))
                f_coeffs = _poly_coeffs_in_var(f_k, "k", max_deg=1)
                if (
                    f_coeffs is not None
                    and len(f_coeffs) == 2
                    and f_coeffs[1] == SymConst(1)
                    and isinstance(f_coeffs[0], SymConst)
                    and f_coeffs[0].value >= 1
                ):
                    c_val = f_coeffs[0].value
                    if c_val == 1:
                        fact_expr: SymExpr = SymFact(k_var)
                    else:
                        fact_expr = SymDiv(
                            SymFact(SymAdd(k_var, SymConst(c_val - 1))),
                            SymFact(SymConst(c_val - 1)),
                        )
                    solved[v] = simplify(SymMul(st_0[v], fact_expr))
                    progress = True
                    continue

        if not progress:
            break

    for v in struct.all_vars:
        if v not in solved:
            limitations.append(
                f"Не вдалося автоматично синтезувати замкнену форму st_k для змінної '{v}'."
            )
            solved[v] = st_0[v]

    return st_0, solved, limitations


def _extract_var_bounds(
    pre_cond: SymBool | None,
) -> tuple[dict[str, int | None], dict[str, int | None]]:
    lowers: dict[str, int | None] = {}
    uppers: dict[str, int | None] = {}

    def tighten_lo(v: str, val: int) -> None:
        cur = lowers.get(v)
        lowers[v] = val if cur is None else max(cur, val)

    def tighten_hi(v: str, val: int) -> None:
        cur = uppers.get(v)
        uppers[v] = val if cur is None else min(cur, val)

    def visit(pred: SymBool) -> None:
        if isinstance(pred, SymAnd):
            visit(pred.left)
            visit(pred.right)
            return
        if isinstance(pred, SymNot):
            s = simplify_bool(pred)
            if not isinstance(s, SymNot):
                visit(s)
            return
        if isinstance(pred, SymCmp):
            diff = simplify(SymSub(pred.left, pred.right))
            fvars = diff.free_vars()
            if len(fvars) == 1:
                v = next(iter(fvars))
                coeffs = _poly_coeffs_in_var(diff, v, max_deg=1)
                if (
                    coeffs is not None
                    and len(coeffs) == 2
                    and isinstance(coeffs[0], SymConst)
                    and isinstance(coeffs[1], SymConst)
                ):
                    a = coeffs[0].value
                    b = coeffs[1].value
                    if b == 1:
                        rhs = -a
                        if pred.op == ">":
                            tighten_lo(v, rhs + 1)
                        elif pred.op == ">=":
                            tighten_lo(v, rhs)
                        elif pred.op == "<":
                            tighten_hi(v, rhs - 1)
                        elif pred.op == "<=":
                            tighten_hi(v, rhs)
                        elif pred.op == "=":
                            tighten_lo(v, rhs)
                            tighten_hi(v, rhs)
                    elif b == -1:
                        if pred.op == ">":
                            tighten_hi(v, a - 1)
                        elif pred.op == ">=":
                            tighten_hi(v, a)
                        elif pred.op == "<":
                            tighten_lo(v, a + 1)
                        elif pred.op == "<=":
                            tighten_lo(v, a)
                        elif pred.op == "=":
                            tighten_lo(v, a)
                            tighten_hi(v, a)

    if pre_cond is not None:
        visit(simplify_bool(pre_cond))
    return lowers, uppers


def _expr_bounds(
    expr: SymExpr,
    lowers: Mapping[str, int | None],
    uppers: Mapping[str, int | None],
) -> tuple[int | None, int | None]:
    """Conservative integer interval ``(lo, hi)`` (``None`` means unbounded)."""
    s = simplify(expr)
    if isinstance(s, SymConst):
        return s.value, s.value
    if isinstance(s, SymVar):
        return lowers.get(s.name), uppers.get(s.name)
    if isinstance(s, SymAdd):
        la, ha = _expr_bounds(s.left, lowers, uppers)
        lb, hb = _expr_bounds(s.right, lowers, uppers)
        lo = (la + lb) if (la is not None and lb is not None) else None
        hi = (ha + hb) if (ha is not None and hb is not None) else None
        return lo, hi
    if isinstance(s, SymSub):
        la, ha = _expr_bounds(s.left, lowers, uppers)
        lb, hb = _expr_bounds(s.right, lowers, uppers)
        def _match_div_mul(mul_node: SymExpr, target: SymExpr) -> SymExpr | None:
            if not isinstance(mul_node, SymMul):
                return None
            div_node: SymDiv | None = None
            other: SymExpr | None = None
            if isinstance(mul_node.left, SymDiv):
                div_node, other = mul_node.left, mul_node.right
            elif isinstance(mul_node.right, SymDiv):
                div_node, other = mul_node.right, mul_node.left
            if (
                div_node is not None
                and other is not None
                and sym_equals(div_node.left, target)
                and sym_equals(div_node.right, other)
            ):
                return other
            return None

        divisor = _match_div_mul(s.right, s.left)
        if divisor is not None:
            ld, hd = _expr_bounds(divisor, lowers, uppers)
            if ld is not None and ld >= 1:
                return 0, (hd - 1 if hd is not None else None)
        neg_divisor = _match_div_mul(s.left, s.right)
        if neg_divisor is not None:
            ld, hd = _expr_bounds(neg_divisor, lowers, uppers)
            if ld is not None and ld >= 1:
                return (-(hd - 1) if hd is not None else None), 0
        lo = (la - hb) if (la is not None and hb is not None) else None
        hi = (ha - lb) if (ha is not None and lb is not None) else None
        return lo, hi
    if isinstance(s, SymMul):
        la, ha = _expr_bounds(s.left, lowers, uppers)
        lb, hb = _expr_bounds(s.right, lowers, uppers)
        if la is not None and lb is not None and la >= 0 and lb >= 0:
            hi = (ha * hb) if (ha is not None and hb is not None) else None
            return la * lb, hi
        if ha is not None and hb is not None and ha <= 0 and hb <= 0:
            lo = (la * lb) if (la is not None and lb is not None) else None
            return ha * hb, lo
        if la is not None and ha is not None and lb is not None and hb is not None:
            prods = [la * lb, la * hb, ha * lb, ha * hb]
            return min(prods), max(prods)
        return None, None
    if isinstance(s, SymDiv):
        la, ha = _expr_bounds(s.left, lowers, uppers)
        lb, hb = _expr_bounds(s.right, lowers, uppers)
        if lb is not None and lb >= 1 and la is not None and la >= 0:
            hi = (ha // lb) if ha is not None else None
            lo = (la // hb) if hb is not None else 0
            return lo, hi
        return None, None
    if isinstance(s, SymMod):
        _, _ = _expr_bounds(s.left, lowers, uppers)
        lb, hb = _expr_bounds(s.right, lowers, uppers)
        if lb is not None and lb >= 1:
            return 0, (hb - 1 if hb is not None else None)
        return None, None
    if isinstance(s, SymPow):
        la, _ha = _expr_bounds(s.base, lowers, uppers)
        lb, _hb = _expr_bounds(s.exp, lowers, uppers)
        if la is not None and lb is not None and lb >= 0:
            if la >= 1:
                return 1, None
            if la >= 0:
                return 0, None
        return None, None
    if isinstance(s, SymFact):
        la, _ = _expr_bounds(s.arg, lowers, uppers)
        if la is not None and la >= 0:
            return 1, None
        return None, None
    return None, None


def _is_provably_positive(
    expr: SymExpr,
    lowers: Mapping[str, int | None],
    uppers: Mapping[str, int | None],
) -> bool:
    lo, _ = _expr_bounds(expr, lowers, uppers)
    return lo is not None and lo >= 1


def _is_provably_nonneg(
    expr: SymExpr,
    lowers: Mapping[str, int | None],
    uppers: Mapping[str, int | None],
) -> bool:
    lo, _ = _expr_bounds(expr, lowers, uppers)
    return lo is not None and lo >= 0


def _solve_exit_iteration(
    while_cond: Bexp,
    hypothesis_k: Mapping[str, SymExpr],
    pre_cond: SymBool | None,
) -> tuple[SymExpr | None, SymBool, str]:
    """Solve for the smallest ``k >= 0`` where ``while_cond(st_k) == false``.

    Returns ``(k_star, cond_k, explanation_note)``.
    """
    lowers, uppers = _extract_var_bounds(pre_cond)
    cond_k = simplify_bool(subst_bool(bexp_to_sym(while_cond), hypothesis_k))

    if isinstance(cond_k, SymBoolConst):
        if not cond_k.value:
            return SymConst(0), cond_k, "Умова циклу одразу хибна (k* = 0)."
        return None, cond_k, "Умова циклу завжди істинна — цикл не завершується."

    if isinstance(cond_k, SymCmp):
        op = cond_k.op
        diff = simplify(SymSub(cond_k.left, cond_k.right))
        coeffs = _poly_coeffs_in_var(diff, "k", max_deg=1)
        if coeffs is not None:
            a_expr = coeffs[0]
            b_expr = coeffs[1] if len(coeffs) > 1 else SymConst(0)
            if b_expr == SymConst(0):
                return (
                    None,
                    cond_k,
                    f"Умова циклу {cond_k.format_unicode()} не залежить від лічильника ітерацій k.",
                )

            norm_op = op
            if op in ("<", "<="):
                a_expr = simplify(SymSub(SymConst(0), a_expr))
                b_expr = simplify(SymSub(SymConst(0), b_expr))
                norm_op = ">" if op == "<" else ">="

            if norm_op in (">", ">="):
                step = simplify(SymSub(SymConst(0), b_expr))
                if not _is_provably_positive(step, lowers, uppers):
                    if _is_provably_positive(b_expr, lowers, uppers) and _is_provably_positive(
                        a_expr, lowers, uppers
                    ):
                        return (
                            None,
                            cond_k,
                            f"Вираз умови {cond_k.format_unicode()} монотонно зростає "
                            "на кожній ітерації — цикл не завершується.",
                        )
                    return (
                        None,
                        cond_k,
                        f"Неможливо гарантувати додатний крок зменшення "
                        f"({step.format_unicode()} > 0) без додаткової передумови.",
                    )

                if norm_op == ">":
                    if step == SymConst(1):
                        if _is_provably_nonneg(a_expr, lowers, uppers):
                            return (
                                a_expr,
                                cond_k,
                                f"Умова {cond_k.format_unicode()} стає хибною "
                                f"при k* = {a_expr.format_unicode()}.",
                            )
                        k_star_if: SymExpr = SymIf(
                            SymCmp(">=", a_expr, SymConst(0)), a_expr, SymConst(0)
                        )
                        return (
                            k_star_if,
                            cond_k,
                            f"Умова {cond_k.format_unicode()} стає хибною "
                            f"при k* = max(0, {a_expr.format_unicode()}).",
                        )
                    if _is_provably_nonneg(a_expr, lowers, uppers):
                        k_star = simplify(SymDiv(SymAdd(a_expr, SymSub(step, SymConst(1))), step))
                        return (
                            k_star,
                            cond_k,
                            f"Найменше k ≥ 0, для якого умова хибна: "
                            f"k* = {k_star.format_unicode()}.",
                        )
                    return (
                        None,
                        cond_k,
                        f"Потрібна умова {a_expr.format_unicode()} ≥ 0 "
                        "для визначення замкненої форми k*.",
                    )

                a_plus_step = simplify(SymAdd(a_expr, step))
                if _is_provably_nonneg(a_plus_step, lowers, uppers):
                    k_star = simplify(SymDiv(a_plus_step, step))
                    return (
                        k_star,
                        cond_k,
                        f"Найменше k ≥ 0, для якого умова хибна: k* = {k_star.format_unicode()}.",
                    )
                return (
                    None,
                    cond_k,
                    f"Потрібна умова {a_plus_step.format_unicode()} ≥ 0 для визначення k*.",
                )

            if norm_op == "!=":
                step = simplify(SymSub(SymConst(0), b_expr))
                if step == SymConst(1) and _is_provably_nonneg(a_expr, lowers, uppers):
                    return (
                        a_expr,
                        cond_k,
                        f"Умова {cond_k.format_unicode()} стає хибною "
                        f"при k* = {a_expr.format_unicode()}.",
                    )

    return (
        None,
        cond_k,
        f"Автоматичне знаходження замкненого k* для умови "
        f"'{cond_k.format_unicode()}' не підтримується.",
    )


def _postcondition_entailed(
    post_eval: SymBool,
    exit_cond_false: SymBool,
    pre_cond: SymBool | None,
) -> tuple[bool, str]:
    """Verify symbolically whether ``post_eval`` follows from preconditions and exit."""
    s_post = simplify_bool(post_eval)
    s_exit = simplify_bool(exit_cond_false)
    lowers, uppers = _extract_var_bounds(pre_cond)

    def check(pred: SymBool) -> tuple[bool, str]:
        if isinstance(pred, SymBoolConst):
            return (pred.value, "Тривіально істинно." if pred.value else "Постумова тотожно хибна.")
        if isinstance(pred, SymAnd):
            ok1, msg1 = check(pred.left)
            if not ok1:
                return False, msg1
            ok2, msg2 = check(pred.right)
            if not ok2:
                return False, msg2
            return True, f"{msg1} {msg2}".strip()
        if isinstance(pred, SymCmp):
            if pred.op == "=":
                if sym_equals(pred.left, pred.right):
                    return True, f"Тотожність {pred.format_unicode()} виконується алгебраїчно."
                return False, f"Рівність {pred.format_unicode()} не зводиться до тотожності."
            if pred.op == "!=":
                diff = simplify(SymSub(pred.left, pred.right))
                lo, hi = _expr_bounds(diff, lowers, uppers)
                if (lo is not None and lo > 0) or (hi is not None and hi < 0):
                    return True, f"Нерівність {pred.format_unicode()} випливає з меж змінних."
            if isinstance(s_exit, SymCmp):
                if pred.op == s_exit.op and sym_equals(
                    SymSub(pred.left, pred.right), SymSub(s_exit.left, s_exit.right)
                ):
                    return (
                        True,
                        f"Умова {pred.format_unicode()} безпосередньо випливає "
                        f"з умови виходу з циклу ({s_exit.format_unicode()}).",
                    )
            diff = simplify(SymSub(pred.left, pred.right))
            lo, hi = _expr_bounds(diff, lowers, uppers)
            if pred.op == ">" and lo is not None and lo > 0:
                return (
                    True,
                    f"Нерівність {pred.format_unicode()} випливає "
                    f"з інтервальних оцінок (різниця ≥ {lo}).",
                )
            if pred.op == ">=" and lo is not None and lo >= 0:
                return (
                    True,
                    f"Нерівність {pred.format_unicode()} випливає "
                    f"з інтервальних оцінок (різниця ≥ {lo}).",
                )
            if pred.op == "<" and hi is not None and hi < 0:
                return (
                    True,
                    f"Нерівність {pred.format_unicode()} випливає "
                    f"з інтервальних оцінок (різниця ≤ {hi}).",
                )
            if pred.op == "<=" and hi is not None and hi <= 0:
                return (
                    True,
                    f"Нерівність {pred.format_unicode()} випливає "
                    f"з інтервальних оцінок (різниця ≤ {hi}).",
                )
            return False, f"Не вдалося символічно довести {pred.format_unicode()}."
        return False, f"Складна логічна формула постумови: {pred.format_unicode()}."

    return check(s_post)


def _synthesize_backward_invariants(
    struct: _ProgramStructure,
    step_map: Mapping[str, SymExpr],
) -> list[tuple[SymExpr, SymExpr, str]]:
    """Synthesize candidate backward-induction invariants ``(lhs, rhs, description)``.

    Variables in ``lhs``/``rhs`` follow ``v_k`` (state ``k`` steps before termination)
    and ``v_0`` (final state at ``k = 0``), matching Practice 3 pp. 20-21.
    """
    if struct.while_node is None:
        return []

    to_k: dict[str, SymExpr] = {v: SymVar(f"{v.lower()}_k") for v in struct.all_vars}
    to_0: dict[str, SymExpr] = {v: SymVar(f"{v.lower()}_0") for v in struct.all_vars}
    k_var = SymVar("k")

    invariants_vars: set[str] = set()
    affine_deltas: dict[str, SymExpr] = {}
    mult_factors: dict[str, SymExpr] = {}
    results: list[tuple[SymExpr, SymExpr, str]] = []

    for v in struct.all_vars:
        rhs = step_map[v]
        if sym_equals(rhs, SymVar(v)):
            invariants_vars.add(v)
            results.append(
                (to_k[v], to_0[v], f"{to_k[v].format_unicode()} = {to_0[v].format_unicode()}")
            )
            continue

    for v in struct.all_vars:
        if v in invariants_vars:
            continue
        rhs = step_map[v]
        delta = simplify(SymSub(rhs, SymVar(v)))
        if delta.free_vars() <= invariants_vars:
            affine_deltas[v] = delta
            d0 = simplify(subst(delta, to_0))
            lhs = to_k[v]
            rhs_inv = simplify(SymSub(to_0[v], SymMul(k_var, d0)))
            results.append((lhs, rhs_inv, f"{lhs.format_unicode()} = {rhs_inv.format_unicode()}"))
            continue
        mult = _extract_linear_multiplier(rhs, v)
        if mult is not None and mult.free_vars() <= invariants_vars:
            mult_factors[v] = mult

    for r_var, m_expr in mult_factors.items():
        m_k = subst(m_expr, to_k)
        m_0 = subst(m_expr, to_0)
        for y_var, d_expr in affine_deltas.items():
            if d_expr == SymConst(-1):
                lhs = simplify(SymMul(to_k[r_var], SymPow(m_k, to_k[y_var])))
                rhs_inv = simplify(SymMul(to_0[r_var], SymPow(m_0, to_0[y_var])))
                results.append(
                    (lhs, rhs_inv, f"{lhs.format_unicode()} = {rhs_inv.format_unicode()}")
                )

    for x_var, dx in affine_deltas.items():
        for r_var, dr in affine_deltas.items():
            if x_var == r_var:
                continue
            if (
                isinstance(dr, SymConst)
                and dr.value > 0
                and x_var < r_var
                or (
                    isinstance(dr, SymConst)
                    and dr.value > 0
                    and not (isinstance(dx, SymConst) and dx.value > 0)
                )
            ):
                neg_dx = simplify(SymSub(SymConst(0), dx))
                lhs = simplify(
                    SymAdd(SymMul(dr, to_k[x_var]), SymMul(subst(neg_dx, to_k), to_k[r_var]))
                )
                rhs_inv = simplify(
                    SymAdd(SymMul(dr, to_0[x_var]), SymMul(subst(neg_dx, to_0), to_0[r_var]))
                )
                results.append(
                    (lhs, rhs_inv, f"{lhs.format_unicode()} = {rhs_inv.format_unicode()}")
                )

    return results


def _parse_backward_invariant_str(text: str, all_vars: list[str]) -> tuple[SymExpr, SymExpr]:
    pred = parse_sym_bool(text)
    if not isinstance(pred, SymCmp) or pred.op != "=":
        raise SiplSemanticError(f"Backward invariant must be an equality '=', got: {text!r}")

    alias_map: dict[str, SymExpr] = {}
    for v in all_vars:
        vk = SymVar(f"{v.lower()}_k")
        v0 = SymVar(f"{v.lower()}_0")
        alias_map[v] = vk
        alias_map[f"{v.lower()}_k"] = vk
        alias_map[f"{v.lower()}k"] = vk
        alias_map[f"{v.lower()}_0"] = v0
        alias_map[f"{v.lower()}0"] = v0
    return subst(pred.left, alias_map), subst(pred.right, alias_map)


def _verify_backward_induction(
    struct: _ProgramStructure,
    step_map: Mapping[str, SymExpr],
    st_0: Mapping[str, SymExpr],
    k_star: SymExpr | None,
    backward_invariants: list[str] | None,
) -> ProofStep:
    if not struct.is_supported_single_loop or struct.while_node is None:
        return ProofStep(
            title="Зворотна індукція (st^{k+1} → st^k)",
            status="inconclusive",
            formula="",
            details="Тіло циклу не є лінійною послідовністю присвоювань для зворотної індукції.",
        )

    if backward_invariants is not None:
        try:
            invs = [
                (*_parse_backward_invariant_str(item, struct.all_vars), item)
                for item in backward_invariants
            ]
        except SiplSemanticError as exc:
            return ProofStep(
                title="Зворотна індукція (st^{k+1} → st^k)",
                status="failed",
                formula=", ".join(backward_invariants),
                details=f"Помилка розбору інваріанту зворотної індукції: {exc}",
            )
    else:
        invs = _synthesize_backward_invariants(struct, step_map)

    if not invs:
        return ProofStep(
            title="Зворотна індукція (st^{k+1} → st^k)",
            status="inconclusive",
            formula="",
            details="Не знайдено інваріантних співвідношень для зворотної індукції.",
        )

    to_k1: dict[str, SymExpr] = {v: SymVar(f"{v.lower()}_(k+1)") for v in struct.all_vars}
    to_0: dict[str, SymExpr] = {v: SymVar(f"{v.lower()}_0") for v in struct.all_vars}

    inv_k1_to_0: dict[str, SymExpr] = {
        f"{v.lower()}_(k+1)": to_0[v] for v in struct.all_vars if sym_equals(step_map[v], SymVar(v))
    }
    step_from_k1: dict[str, SymExpr] = {
        f"{v.lower()}_k": simplify(subst(subst(step_map[v], to_k1), inv_k1_to_0))
        for v in struct.all_vars
    }
    lift_to_k1: dict[str, SymExpr] = {
        f"{v.lower()}_k": inv_k1_to_0.get(f"{v.lower()}_(k+1)", to_k1[v]) for v in struct.all_vars
    }
    lift_to_k1["k"] = SymAdd(SymVar("k"), SymConst(1))

    base_map: dict[str, SymExpr] = {f"{v.lower()}_k": to_0[v] for v in struct.all_vars}
    base_map["k"] = SymConst(0)

    verified_formulas: list[str] = []
    failed_msgs: list[str] = []

    for lhs, rhs, _label in invs:
        b_lhs = simplify(subst(lhs, base_map))
        b_rhs = simplify(subst(rhs, base_map))
        if not sym_equals(b_lhs, b_rhs):
            failed_msgs.append(
                f"База (k=0) не виконується для {lhs.format_unicode()} = {rhs.format_unicode()}: "
                f"{b_lhs.format_unicode()} ≠ {b_rhs.format_unicode()}."
            )
            continue

        diff_k_applied = simplify(subst(SymSub(lhs, rhs), step_from_k1))
        diff_k1 = simplify(subst(SymSub(lhs, rhs), lift_to_k1))
        if not sym_equals(diff_k_applied, diff_k1):
            failed_msgs.append(
                f"Крок (k→k+1) не виконується для {lhs.format_unicode()} = {rhs.format_unicode()}: "
                f"після переходу st^{{k+1}} → st^k маємо "
                f"({diff_k_applied.format_unicode()}) ≠ ({diff_k1.format_unicode()})."
            )
            continue

        verified_formulas.append(f"{lhs.format_unicode()} = {rhs.format_unicode()}")

    formula_str = (
        "; ".join(verified_formulas)
        if verified_formulas
        else "; ".join(f"{lhs.format_unicode()} = {rhs.format_unicode()}" for lhs, rhs, _ in invs)
    )
    if failed_msgs:
        return ProofStep(
            title="Зворотна індукція (st^{k+1} → st^k)",
            status="failed",
            formula=formula_str,
            details=" ".join(failed_msgs),
        )

    exit_note = ""
    if k_star is not None:
        st0_str = ", ".join(f"{v.lower()}_n = {e.format_unicode()}" for v, e in st_0.items())
        exit_note = (
            f" При k = n (стан st^n = st₀: {st0_str}) з умови завершення "
            f"fb(st⁰) = false отримуємо k* = {k_star.format_unicode()}."
        )
    return ProofStep(
        title="Зворотна індукція (st^{k+1} → st^k)",
        status="proved",
        formula=formula_str,
        details=(
            "База k = 0 та крок переходу st^{k+1} → st^k доведені алгебраїчно "
            f"для всіх співвідношень.{exit_note}"
        ),
    )


def _build_eval_aliases(
    init_dict: Mapping[str, int],
    init_symbols: Mapping[str, str],
) -> dict[str, int]:
    """Bind both uppercase program vars and lowercase initial symbols to initial values."""
    env = dict(init_dict)
    for var, sym in init_symbols.items():
        if var in init_dict:
            env[sym] = init_dict[var]
            env[f"{var}_0"] = init_dict[var]
            env[f"{var.lower()}_0"] = init_dict[var]
            env[f"{var.lower()}0"] = init_dict[var]
    return env


def find_counterexamples(
    program: Program,
    *,
    precondition: str | None = None,
    postcondition: str | None = None,
    hypothesis: Mapping[str, str] | Mapping[str, SymExpr] | None = None,
    invariant: str | None = None,
    test_domains: Mapping[str, list[int]] | None = None,
    max_steps: int = 1000,
    max_cases: int = 150,
) -> list[Counterexample]:
    """Search concrete inputs violating hypothesis, invariant, postcondition, or termination."""
    struct = _analyze_structure(program)
    pre_sym = parse_sym_bool(precondition) if precondition else None
    post_sym = parse_sym_bool(postcondition) if postcondition else None
    inv_sym = parse_sym_bool(invariant) if invariant else None

    hyp_sym: dict[str, SymExpr] | None = None
    if hypothesis is not None:
        hyp_sym = {
            var: (val if isinstance(val, SymExpr) else parse_sym_expr(val))
            for var, val in hypothesis.items()
        }

    input_vars = struct.input_vars or struct.all_vars
    if not input_vars:
        candidate_states: list[dict[str, int]] = [{}]
    else:
        if len(input_vars) <= 2:
            default_vals = [1, 2, 3, 4, 5, 6, 0, -1]
        elif len(input_vars) == 3:
            default_vals = [1, 2, 3, 4, 0, -1]
        else:
            default_vals = [1, 2, 3, 0]

        domains = [
            list(test_domains[v]) if (test_domains and v in test_domains) else default_vals
            for v in input_vars
        ]
        candidate_states = []
        for combo in itertools.product(*domains):
            init_dict = dict(zip(input_vars, combo, strict=True))
            if pre_sym is not None:
                alias_env = _build_eval_aliases(init_dict, struct.init_symbols)
                try:
                    if not eval_sym_bool(pre_sym, alias_env):
                        continue
                except SiplSemanticError:
                    continue
            candidate_states.append(init_dict)
            if len(candidate_states) >= max_cases:
                break

    counterexamples: list[Counterexample] = []
    main_while_id = struct.while_node.node_id if struct.while_node is not None else None

    for init_dict in candidate_states:
        result = run_program(program, State(init_dict), max_steps=max_steps)
        if not result.is_defined or result.final_state is None:
            counterexamples.append(
                Counterexample(
                    initial_state=init_dict,
                    iteration=None,
                    expected="defined terminating execution",
                    actual=result.error,
                    reason=(
                        f"Програма не завершилася або виникла помилка "
                        f"({result.error_code}): {result.error}"
                    ),
                )
            )
            if len(counterexamples) >= 5:
                break
            continue

        init_aliases = _build_eval_aliases(init_dict, struct.init_symbols)

        if main_while_id is not None and (hyp_sym is not None or inv_sym is not None):
            iter_events = [
                ev
                for ev in result.trace.events
                if ev.event_type == "ConditionEvaluated"
                and ev.details.get("parent_node_id") == main_while_id
            ]
            found_in_loop = False
            for k_idx, ev in enumerate(iter_events):
                concrete_st = ev.state
                if hyp_sym is not None:
                    for var, expr in hyp_sym.items():
                        eval_env = dict(init_aliases)
                        eval_env["k"] = k_idx
                        try:
                            expected_val = eval_sym_expr(expr, eval_env)
                        except SiplSemanticError as exc:
                            counterexamples.append(
                                Counterexample(
                                    initial_state=init_dict,
                                    iteration=k_idx,
                                    expected=f"defined {var}",
                                    actual=str(exc),
                                    reason=(
                                        f"Неможливо обчислити гіпотезу для '{var}' "
                                        f"при k={k_idx}: {exc}"
                                    ),
                                )
                            )
                            found_in_loop = True
                            break
                        actual_val = concrete_st.get(var)
                        if actual_val != expected_val:
                            counterexamples.append(
                                Counterexample(
                                    initial_state=init_dict,
                                    iteration=k_idx,
                                    expected={var: expected_val},
                                    actual={var: actual_val},
                                    reason=(
                                        f"Невідповідність гіпотези для '{var}' "
                                        f"на ітерації k={k_idx}: "
                                        f"очікувалося {expected_val}, отримано {actual_val}"
                                    ),
                                )
                            )
                            found_in_loop = True
                            break
                    if found_in_loop:
                        break

                if inv_sym is not None:
                    eval_env = dict(init_aliases)
                    eval_env.update(concrete_st)
                    eval_env["k"] = k_idx
                    try:
                        inv_holds = eval_sym_bool(inv_sym, eval_env)
                    except SiplSemanticError:
                        inv_holds = False
                    if not inv_holds:
                        counterexamples.append(
                            Counterexample(
                                initial_state=init_dict,
                                iteration=k_idx,
                                expected=True,
                                actual=False,
                                reason=(
                                    f"Інваріант '{invariant}' порушено на ітерації "
                                    f"k={k_idx} (стан {concrete_st})"
                                ),
                            )
                        )
                        found_in_loop = True
                        break
            if found_in_loop:
                if len(counterexamples) >= 5:
                    break
                continue

        if post_sym is not None:
            final_dict = result.final_state.to_dict()
            eval_env = dict(init_aliases)
            eval_env.update(final_dict)
            try:
                post_holds = eval_sym_bool(post_sym, eval_env)
            except SiplSemanticError as exc:
                post_holds = False
                reason = f"Помилка обчислення постумови '{postcondition}': {exc}"
            else:
                reason = f"Постумова '{postcondition}' хибна для фінального стану {final_dict}"
            if not post_holds:
                counterexamples.append(
                    Counterexample(
                        initial_state=init_dict,
                        iteration=None,
                        expected=postcondition,
                        actual=final_dict,
                        reason=reason,
                    )
                )
                if len(counterexamples) >= 5:
                    break

    return counterexamples


def _with_init_aliases(
    state_map: Mapping[str, SymExpr],
    init_state: Mapping[str, SymExpr],
) -> dict[str, SymExpr]:
    env: dict[str, SymExpr] = {}
    for var, sym in init_state.items():
        env[f"{var}_0"] = sym
        env[f"{var.lower()}_0"] = sym
        env[f"{var.lower()}0"] = sym
    env.update(state_map)
    return env


def _format_sym_map(mapping: Mapping[str, SymExpr]) -> dict[str, str]:
    return {k: v.format_unicode() for k, v in mapping.items()}


def _build_ukrainian_explanation(
    *,
    init_state: Mapping[str, SymExpr],
    st_0: Mapping[str, SymExpr],
    precondition: str | None,
    loop_cond_str: str,
    hyp_k: Mapping[str, SymExpr],
    hyp_source: str,
    base_case: ProofStep,
    inductive_step: ProofStep,
    termination_and_exit: ProofStep,
    backward_induction: ProofStep | None,
    counterexamples: list[Counterexample],
    limitations: list[str],
    overall_status: str,
) -> str:
    lines: list[str] = []
    lines.append(f"Статус доведення: {overall_status}")
    lines.append(f"Початковий символьний стан: st = {SymState(dict(init_state)).format_unicode()}")
    if precondition:
        lines.append(f"Передумова: {precondition}")
    lines.append(f"Стан до початку циклу: st₀ = {SymState(dict(st_0)).format_unicode()}")
    if loop_cond_str:
        lines.append(f"Умова циклу: {loop_cond_str}")
    src_ua = "синтезована" if hyp_source == "synthesized" else "задана користувачем"
    lines.append(f"Індукційна гіпотеза ({src_ua}): st_k = {SymState(dict(hyp_k)).format_unicode()}")
    lines.append("")
    lines.append(f"1. {base_case.title} [{base_case.status}]: {base_case.formula}")
    lines.append(f"   {base_case.details}")
    lines.append(f"2. {inductive_step.title} [{inductive_step.status}]: {inductive_step.formula}")
    lines.append(f"   {inductive_step.details}")
    lines.append(
        f"3. {termination_and_exit.title} [{termination_and_exit.status}]: "
        f"{termination_and_exit.formula}"
    )
    lines.append(f"   {termination_and_exit.details}")
    if backward_induction is not None:
        lines.append(
            f"4. {backward_induction.title} [{backward_induction.status}]: "
            f"{backward_induction.formula}"
        )
        lines.append(f"   {backward_induction.details}")
    if counterexamples:
        lines.append("")
        lines.append("Знайдені контрприклади:")
        for cx in counterexamples:
            lines.append(f" - st={cx.initial_state}: {cx.reason}")
    if limitations:
        lines.append("")
        lines.append("Обмеження автоматизації:")
        for lim in limitations:
            lines.append(f" - {lim}")
    return "\n".join(lines)


def prove_program(
    program: Program,
    *,
    precondition: str | None = None,
    postcondition: str | None = None,
    hypothesis: Mapping[str, str] | None = None,
    invariant: str | None = None,
    backward_invariants: list[str] | None = None,
    mode: str = "hybrid",
    test_domains: Mapping[str, list[int]] | None = None,
) -> ProofReport:
    """Perform automated forward/backward inductive correctness verification on ``program``."""
    if mode not in ("forward_induction", "backward_induction", "hybrid"):
        raise SiplSemanticError(
            f"Invalid proof mode {mode!r}; expected "
            "'forward_induction', 'backward_induction', or 'hybrid'"
        )

    struct = _analyze_structure(program)
    init_state, st_0 = _compute_pre_loop_state(struct)

    pre_sym_raw = parse_sym_bool(precondition) if precondition else None
    pre_sym_norm = subst_bool(pre_sym_raw, init_state) if pre_sym_raw is not None else None

    if struct.while_node is None or struct.has_unsupported_control_flow:
        limitations = list(struct.limitations)
        loop_cond_str = (
            bexp_to_sym(struct.while_node.cond).format_unicode()
            if struct.while_node is not None
            else ""
        )

        if struct.while_node is None and not struct.has_unsupported_control_flow:
            cxs = find_counterexamples(
                program,
                precondition=precondition,
                postcondition=postcondition,
                test_domains=test_domains,
            )
            post_ok = True
            post_msg = "Програма не містить циклів; символьне виконання завершено."
            if postcondition:
                post_sym = parse_sym_bool(postcondition)
                post_env = _with_init_aliases(st_0, init_state)
                post_eval = simplify_bool(subst_bool(post_sym, post_env))
                post_ok, post_msg = _postcondition_entailed(
                    post_eval, SymBoolConst(True), pre_sym_norm
                )
            status = "disproved" if cxs else ("proved" if post_ok else "partial")
            base_step = ProofStep(
                title="База індукції (k = 0)",
                status="proved",
                formula=SymState(st_0).format_unicode(),
                details="Програма не містить циклів; початковий стан st₀ обчислено безпосередньо.",
            )
            step_step = ProofStep(
                title="Крок індукції (k → k + 1)",
                status="proved",
                formula="id",
                details="Цикли відсутні; крок індукції не потрібен.",
            )
            exit_step = ProofStep(
                title="Умова виходу та постумова",
                status="counterexample" if cxs else ("proved" if post_ok else "inconclusive"),
                formula=postcondition or "завершення без циклу",
                details=post_msg,
            )
            explanation = _build_ukrainian_explanation(
                init_state=init_state,
                st_0=st_0,
                precondition=precondition,
                loop_cond_str="",
                hyp_k=st_0,
                hyp_source="synthesized",
                base_case=base_step,
                inductive_step=step_step,
                termination_and_exit=exit_step,
                backward_induction=None,
                counterexamples=cxs,
                limitations=limitations,
                overall_status=status,
            )
            return ProofReport(
                program_summary="Лінійна програма без циклу while",
                status=status,
                mode=mode,
                initial_symbolic_state=_format_sym_map(init_state),
                pre_loop_state=_format_sym_map(st_0),
                loop_condition="",
                hypothesis_k=_format_sym_map(st_0),
                hypothesis_source="synthesized",
                base_case=base_step,
                inductive_step=step_step,
                termination_and_exit=exit_step,
                backward_induction=None,
                counterexamples=cxs,
                limitations=limitations,
                explanation_text=explanation,
            )

        user_hyp_parsed: dict[str, SymExpr] | None = None
        hyp_source = "synthesized"
        if hypothesis is not None:
            user_hyp_parsed = {v: parse_sym_expr(expr) for v, expr in hypothesis.items()}
            hyp_source = "user"
        cxs = find_counterexamples(
            program,
            precondition=precondition,
            postcondition=postcondition,
            hypothesis=user_hyp_parsed,
            invariant=invariant,
            test_domains=test_domains,
        )
        hyp_display = user_hyp_parsed or st_0
        checked_concrete = bool(invariant or postcondition) and not cxs
        status = "disproved" if cxs else ("partial" if checked_concrete else "unsupported")
        inconclusive_details = (
            "Автоматичне символьне доведення неповне через розгалуження/вкладення; "
            + (
                "конкретна перевірка на сітці тестів не виявила контрприкладів."
                if not cxs
                else "виявлено контрприклад."
            )
        )
        base_step = ProofStep(
            title="База індукції (k = 0)",
            status="inconclusive",
            formula=SymState(hyp_display).format_unicode(),
            details=inconclusive_details,
        )
        ind_step = ProofStep(
            title="Крок індукції (k → k + 1)",
            status="inconclusive",
            formula="",
            details=(
                "Тіло циклу містить розгалуження або вкладені цикли; "
                "замкнений символьний крок не синтезовано."
            ),
        )
        exit_step = ProofStep(
            title="Умова виходу та постумова",
            status="counterexample" if cxs else "inconclusive",
            formula=postcondition or loop_cond_str,
            details=cxs[0].reason if cxs else inconclusive_details,
        )
        unsupported_bwd_step = (
            ProofStep(
                title="Зворотна індукція (st^{k+1} → st^k)",
                status="inconclusive",
                formula="",
                details="Зворотна індукція не підтримується для розгалужених тіл циклу.",
            )
            if mode in ("backward_induction", "hybrid")
            else None
        )
        explanation = _build_ukrainian_explanation(
            init_state=init_state,
            st_0=st_0,
            precondition=precondition,
            loop_cond_str=loop_cond_str,
            hyp_k=hyp_display,
            hyp_source=hyp_source,
            base_case=base_step,
            inductive_step=ind_step,
            termination_and_exit=exit_step,
            backward_induction=unsupported_bwd_step,
            counterexamples=cxs,
            limitations=limitations,
            overall_status=status,
        )
        return ProofReport(
            program_summary="Програма з циклом while (складний потік керування)",
            status=status,
            mode=mode,
            initial_symbolic_state=_format_sym_map(init_state),
            pre_loop_state=_format_sym_map(st_0),
            loop_condition=loop_cond_str,
            hypothesis_k=_format_sym_map(hyp_display),
            hypothesis_source=hyp_source,
            base_case=base_step,
            inductive_step=ind_step,
            termination_and_exit=exit_step,
            backward_induction=unsupported_bwd_step,
            counterexamples=cxs,
            limitations=limitations,
            explanation_text=explanation,
        )

    assert struct.while_node is not None
    loop_cond_str = bexp_to_sym(struct.while_node.cond).format_unicode()
    synth_st_0, synth_hyp_k, limitations = synthesize_loop_hypothesis(program, precondition)
    st_0 = synth_st_0

    if hypothesis is not None:
        hyp_source = "user"
        hyp_k = dict(synth_hyp_k)
        for v, raw_expr in hypothesis.items():
            hyp_k[v] = simplify(parse_sym_expr(raw_expr))
    else:
        hyp_source = "synthesized"
        hyp_k = synth_hyp_k

    k_zero_env = {"k": SymConst(0)}
    base_mismatches: list[str] = []
    for v in struct.all_vars:
        lhs_0 = simplify(subst(hyp_k[v], k_zero_env))
        rhs_0 = simplify(st_0[v])
        if not sym_equals(lhs_0, rhs_0):
            base_mismatches.append(f"{v}: {lhs_0.format_unicode()} ≠ {rhs_0.format_unicode()}")

    if base_mismatches:
        base_at_zero = {v: simplify(subst(hyp_k[v], k_zero_env)) for v in struct.all_vars}
        base_step = ProofStep(
            title="База індукції (k = 0)",
            status="failed",
            formula=f"st_k|_{{k=0}} = {SymState(base_at_zero).format_unicode()}",
            details="База індукції не збігається зі станом st₀: " + "; ".join(base_mismatches),
        )
    else:
        base_step = ProofStep(
            title="База індукції (k = 0)",
            status="proved",
            formula=f"st_k|_{{k=0}} = {SymState(st_0).format_unicode()} = st₀",
            details="При підстановці k = 0 стан st_k збігається зі станом до циклу st₀.",
        )

    step_map = _compute_loop_step_map(struct.while_node.body, struct.all_vars)
    actual_next = {v: simplify(subst(step_map[v], hyp_k)) for v in struct.all_vars}
    k_plus_1_env = {"k": SymAdd(SymVar("k"), SymConst(1))}
    expected_next = {v: simplify(subst(hyp_k[v], k_plus_1_env)) for v in struct.all_vars}

    step_mismatches: list[str] = []
    for v in struct.all_vars:
        if not sym_equals(actual_next[v], expected_next[v]):
            step_mismatches.append(
                f"{v}: тіло дає {actual_next[v].format_unicode()}, "
                f"гіпотеза вимагає {expected_next[v].format_unicode()}"
            )

    if step_mismatches:
        ind_step = ProofStep(
            title="Крок індукції (k → k + 1)",
            status="failed",
            formula=f"fs(st_k) = {SymState(actual_next).format_unicode()}",
            details="Крок індукції спростовано: " + "; ".join(step_mismatches),
        )
    else:
        ind_step = ProofStep(
            title="Крок індукції (k → k + 1)",
            status="proved",
            formula=f"fs(st_k) = {SymState(expected_next).format_unicode()} = st_{{k+1}}",
            details="Застосування семантики тіла циклу до st_k дає точний стан st_{k+1}.",
        )

    k_star, cond_k, exit_note = _solve_exit_iteration(struct.while_node.cond, hyp_k, pre_sym_norm)

    cxs = find_counterexamples(
        program,
        precondition=precondition,
        postcondition=postcondition,
        hypothesis=hyp_k,
        invariant=invariant,
        test_domains=test_domains,
    )

    if k_star is None:
        exit_status = "counterexample" if cxs else "inconclusive"
        exit_step = ProofStep(
            title="Умова виходу та завершуваність",
            status=exit_status,
            formula=f"fb(st_k) = ({cond_k.format_unicode()})",
            details=cxs[0].reason if cxs else exit_note,
        )
    else:
        exit_env = {"k": k_star}
        st_exit = {v: simplify(subst(hyp_k[v], exit_env)) for v in struct.all_vars}
        for ep_assign in struct.epilogue:
            st_exit[ep_assign.var] = simplify(subst(aexp_to_sym(ep_assign.expr), st_exit))
        exit_cond_false = simplify_bool(
            SymNot(subst_bool(bexp_to_sym(struct.while_node.cond), st_exit))
        )
        post_ok = True
        post_details = ""
        if postcondition is not None:
            post_sym = parse_sym_bool(postcondition)
            post_eval = simplify_bool(subst_bool(post_sym, _with_init_aliases(st_exit, init_state)))
            post_ok, post_details = _postcondition_entailed(
                post_eval, exit_cond_false, pre_sym_norm
            )
        if cxs:
            exit_status = "counterexample"
            exit_details = cxs[0].reason
        elif postcondition is not None and not post_ok:
            exit_status = "failed"
            exit_details = f"{exit_note} {post_details}"
        else:
            exit_status = "proved"
            exit_details = f"{exit_note} Заключний стан: {SymState(st_exit).format_unicode()}. " + (
                post_details or "Завершуваність та вихід підтверджено."
            )
        exit_step = ProofStep(
            title="Умова виходу та завершуваність",
            status=exit_status,
            formula=(
                f"k* = {k_star.format_unicode()}; st_{{k*}} = {SymState(st_exit).format_unicode()}"
            ),
            details=exit_details.strip(),
        )

    bwd_step: ProofStep | None = None
    if mode in ("backward_induction", "hybrid"):
        bwd_step = _verify_backward_induction(struct, step_map, st_0, k_star, backward_invariants)

    if (
        cxs
        or base_step.status == "failed"
        or ind_step.status == "failed"
        or exit_step.status
        in (
            "failed",
            "counterexample",
        )
    ):
        overall_status = "disproved"
    elif mode == "forward_induction":
        if (
            base_step.status == "proved"
            and ind_step.status == "proved"
            and exit_step.status == "proved"
        ):
            overall_status = "proved"
        else:
            overall_status = "partial"
    elif mode == "backward_induction":
        if bwd_step is not None and bwd_step.status == "proved" and exit_step.status == "proved":
            overall_status = "proved"
        elif bwd_step is not None and bwd_step.status == "failed":
            overall_status = "disproved"
        else:
            overall_status = "partial"
    else:
        if (
            base_step.status == "proved"
            and ind_step.status == "proved"
            and exit_step.status == "proved"
            and (bwd_step is None or bwd_step.status != "failed")
        ):
            if (
                backward_invariants is not None
                and bwd_step is not None
                and bwd_step.status != "proved"
            ):
                overall_status = "partial"
            else:
                overall_status = "proved"
        elif bwd_step is not None and bwd_step.status == "failed":
            overall_status = "disproved"
        else:
            overall_status = "partial"

    explanation = _build_ukrainian_explanation(
        init_state=init_state,
        st_0=st_0,
        precondition=precondition,
        loop_cond_str=loop_cond_str,
        hyp_k=hyp_k,
        hyp_source=hyp_source,
        base_case=base_step,
        inductive_step=ind_step,
        termination_and_exit=exit_step,
        backward_induction=bwd_step,
        counterexamples=cxs,
        limitations=limitations,
        overall_status=overall_status,
    )

    return ProofReport(
        program_summary=f"Цикл while ({loop_cond_str}) з {len(struct.all_vars)} змінними",
        status=overall_status,
        mode=mode,
        initial_symbolic_state=_format_sym_map(init_state),
        pre_loop_state=_format_sym_map(st_0),
        loop_condition=loop_cond_str,
        hypothesis_k=_format_sym_map(hyp_k),
        hypothesis_source=hyp_source,
        base_case=base_step,
        inductive_step=ind_step,
        termination_and_exit=exit_step,
        backward_induction=bwd_step,
        counterexamples=cxs,
        limitations=limitations,
        explanation_text=explanation,
    )
