"""Semantic terms of algebra A_SIPL and step-by-step term derivation."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from sipl.ast import (
    Aexp,
    Assign,
    ASTNode,
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
from sipl.diagnostics import Diagnostic, SiplSemanticError, SourceSpan


def _semantic_error(message: str, span: SourceSpan | None = None) -> SiplSemanticError:
    diag = (
        Diagnostic(code="E_SEMANTIC", message=message, span=span)
        if span is not None
        else None
    )
    return SiplSemanticError(message, diagnostic=diag)

_AEXP_OP_MAP: dict[str, tuple[str, str]] = {
    "+": ("add", "NS_A_Add"),
    "-": ("sub", "NS_A_Sub"),
    "*": ("mult", "NS_A_Mult"),
    "div": ("div", "NS_A_Div"),
    "mod": ("mod", "NS_A_Mod"),
}

_CMP_OP_MAP: dict[str, tuple[str, str]] = {
    "=": ("eq", "NS_B_eq"),
    ">": ("gr", "NS_B_gr"),
    ">=": ("gre", "NS_B_gre"),
    "<": ("less", "NS_B_less"),
    "<=": ("leq", "NS_B_leq"),
    "!=": ("neq", "NS_B_neq"),
}

_BOOL_OP_MAP: dict[str, tuple[str, str]] = {
    "or": ("or", "NS_B_or"),
    "and": ("and", "NS_B_and"),
}


def _serialize_term_value(value: Any) -> Any:
    if isinstance(value, SemanticTerm):
        return value.to_dict()
    if isinstance(value, SourceSpan):
        return value.to_dict()
    if isinstance(value, list):
        return [_serialize_term_value(item) for item in value]
    return value


def _unwrap_blocks(term: TFS) -> TFS:
    cur = term
    while isinstance(cur, BlockTerm):
        cur = cur.inner
    return cur


def _format_seq_child_unicode(term: TFS, *, is_right: bool) -> str:
    if isinstance(term, BlockTerm):
        unwrapped = _unwrap_blocks(term)
        if isinstance(unwrapped, SeqTerm):
            return f"({unwrapped.format_unicode()})"
        return unwrapped.format_unicode()
    if is_right and isinstance(term, SeqTerm):
        return f"({term.format_unicode()})"
    return term.format_unicode()


def _format_seq_child_latex(term: TFS, *, is_right: bool) -> str:
    if isinstance(term, BlockTerm):
        unwrapped = _unwrap_blocks(term)
        if isinstance(unwrapped, SeqTerm):
            return f"({unwrapped.format_latex()})"
        return unwrapped.format_latex()
    if is_right and isinstance(term, SeqTerm):
        return f"({term.format_latex()})"
    return term.format_latex()


def _format_compound_arg_unicode(term: TFS) -> str:
    if isinstance(term, BlockTerm):
        return _unwrap_blocks(term).format_unicode()
    return term.format_unicode()


def _format_compound_arg_latex(term: TFS) -> str:
    if isinstance(term, BlockTerm):
        return _unwrap_blocks(term).format_latex()
    return term.format_latex()


@dataclass(frozen=True, slots=True)
class SemanticTerm:
    """Base class for all semantic terms of the program algebra ``A_SIPL``."""

    term_id: str = field(default="", kw_only=True)
    ast_node_id: str | None = field(default=None, kw_only=True)
    span: SourceSpan | None = field(default=None, kw_only=True)

    def format_unicode(self) -> str:
        """Render this semantic term in course Unicode notation."""
        raise NotImplementedError

    def format_latex(self) -> str:
        """Render this semantic term in LaTeX math notation."""
        raise NotImplementedError

    def to_dict(self) -> dict[str, Any]:
        """Serialize this semantic term and its children to a JSON-compatible dictionary."""
        result: dict[str, Any] = {
            "kind": self.__class__.__name__,
            "term_id": self.term_id,
            "unicode": self.format_unicode(),
            "latex": self.format_latex(),
        }
        if self.ast_node_id is not None:
            result["ast_node_id"] = self.ast_node_id
        if self.span is not None:
            result["span"] = self.span.to_dict()

        for cls in self.__class__.__mro__:
            annotations = getattr(cls, "__annotations__", {})
            for attr in annotations:
                if attr in ("term_id", "ast_node_id", "span") or attr.startswith("_"):
                    continue
                val = getattr(self, attr)
                if val is not None:
                    result[attr] = _serialize_term_value(val)
        return result


@dataclass(frozen=True, slots=True)
class TFA(SemanticTerm):
    """Base class for nominative arithmetic function terms (``TFA``)."""


@dataclass(frozen=True, slots=True)
class TFB(SemanticTerm):
    """Base class for nominative predicate terms (``TFB``)."""


@dataclass(frozen=True, slots=True)
class TFS(SemanticTerm):
    """Base class for binominative statement transformer terms (``TFS``)."""


@dataclass(frozen=True, slots=True)
class ConstNumTerm(TFA):
    """Constant nominative arithmetic function ``n̄`` (``NS_A_Num``).

    Standardizes Unicode formatting as ``f"{self.value}\\u0304"`` (e.g., ``0̄``,
    ``1̄``, ``12̄``, ``-1̄``) and LaTeX formatting as ``\\overline{n}``.
    """

    value: int

    def format_unicode(self) -> str:
        return f"{self.value}\u0304"

    def format_latex(self) -> str:
        return f"\\overline{{{self.value}}}"


@dataclass(frozen=True, slots=True)
class DerefTerm(TFA):
    """Variable dereferencing nominative function ``x⇒`` (``NS_A_Var``)."""

    var: str

    def format_unicode(self) -> str:
        return f"{self.var}\u21d2"

    def format_latex(self) -> str:
        return f"{self.var}\\Rightarrow"


@dataclass(frozen=True, slots=True)
class SuperposAexpTerm(TFA):
    """Superposition of an n-ary arithmetic operation with ``TFA`` arguments."""

    op_name: str
    args: list[TFA]

    def format_unicode(self) -> str:
        rendered_args = ", ".join(arg.format_unicode() for arg in self.args)
        return f"S^{len(self.args)}({self.op_name}, {rendered_args})"

    def format_latex(self) -> str:
        rendered_args = ", ".join(arg.format_latex() for arg in self.args)
        return f"S^{{{len(self.args)}}}(\\mathrm{{{self.op_name}}}, {rendered_args})"


@dataclass(frozen=True, slots=True)
class SuperposCmpTerm(TFB):
    """Superposition of a binary comparison predicate with two ``TFA`` arguments."""

    op_name: str
    left: TFA
    right: TFA

    def format_unicode(self) -> str:
        return f"S^2({self.op_name}, {self.left.format_unicode()}, {self.right.format_unicode()})"

    def format_latex(self) -> str:
        return (
            f"S^{{2}}(\\mathrm{{{self.op_name}}}, "
            f"{self.left.format_latex()}, {self.right.format_latex()})"
        )


@dataclass(frozen=True, slots=True)
class SuperposBoolTerm(TFB):
    """Superposition of a boolean connective (``or``, ``and``, ``neg``) with ``TFB`` args."""

    op_name: str
    args: list[TFB]

    def format_unicode(self) -> str:
        rendered_args = ", ".join(arg.format_unicode() for arg in self.args)
        return f"S^{len(self.args)}({self.op_name}, {rendered_args})"

    def format_latex(self) -> str:
        rendered_args = ", ".join(arg.format_latex() for arg in self.args)
        return f"S^{{{len(self.args)}}}(\\mathrm{{{self.op_name}}}, {rendered_args})"


@dataclass(frozen=True, slots=True)
class AssignTerm(TFS):
    """Assignment composition ``AS^x(fa)`` (``NS_Stm_As``)."""

    var: str
    expr: TFA

    def format_unicode(self) -> str:
        return f"AS^{self.var}({self.expr.format_unicode()})"

    def format_latex(self) -> str:
        return f"AS^{{{self.var}}}({self.expr.format_latex()})"


@dataclass(frozen=True, slots=True)
class SeqTerm(TFS):
    """Sequential composition ``fs1 · fs2`` (``NS_Stm_Seq``)."""

    left: TFS
    right: TFS

    def format_unicode(self) -> str:
        left_str = _format_seq_child_unicode(self.left, is_right=False)
        right_str = _format_seq_child_unicode(self.right, is_right=True)
        return f"{left_str} \u00b7 {right_str}"

    def format_latex(self) -> str:
        left_str = _format_seq_child_latex(self.left, is_right=False)
        right_str = _format_seq_child_latex(self.right, is_right=True)
        return f"{left_str} \\cdot {right_str}"


@dataclass(frozen=True, slots=True)
class IfTerm(TFS):
    """Conditional branching composition ``IF(fb, fs1, fs2)`` (``NS_Stm_If``)."""

    cond: TFB
    then_term: TFS
    else_term: TFS

    def format_unicode(self) -> str:
        then_str = _format_compound_arg_unicode(self.then_term)
        else_str = _format_compound_arg_unicode(self.else_term)
        return f"IF({self.cond.format_unicode()}, {then_str}, {else_str})"

    def format_latex(self) -> str:
        then_str = _format_compound_arg_latex(self.then_term)
        else_str = _format_compound_arg_latex(self.else_term)
        return f"\\mathrm{{IF}}({self.cond.format_latex()}, {then_str}, {else_str})"


@dataclass(frozen=True, slots=True)
class WhileTerm(TFS):
    """Loop composition ``WH(fb, fs)`` (``NS_Stm_Wh``)."""

    cond: TFB
    body: TFS

    def format_unicode(self) -> str:
        body_str = _format_compound_arg_unicode(self.body)
        return f"WH({self.cond.format_unicode()}, {body_str})"

    def format_latex(self) -> str:
        body_str = _format_compound_arg_latex(self.body)
        return f"\\mathrm{{WH}}({self.cond.format_latex()}, {body_str})"


@dataclass(frozen=True, slots=True)
class BlockTerm(TFS):
    """Compound block wrapper ``(fs)`` recording ``NS_Stm_BE`` in derivation traces."""

    inner: TFS

    def format_unicode(self) -> str:
        return self.inner.format_unicode()

    def format_latex(self) -> str:
        return self.inner.format_latex()


@dataclass(frozen=True, slots=True)
class IdTerm(TFS):
    """Identity transformer ``id`` (``NS_Stm_skip``)."""

    def format_unicode(self) -> str:
        return "id"

    def format_latex(self) -> str:
        return "\\mathrm{id}"


@dataclass(frozen=True, slots=True)
class DerivationStep:
    """Single replacement rule application during ``sem_*`` term construction."""

    step_index: int
    rule_name: str
    source_form: str
    target_form: str
    unifier: dict[str, str]
    ast_node_id: str | None
    span: SourceSpan | None

    def to_dict(self) -> dict[str, Any]:
        """Serialize this derivation step into a JSON-compatible dictionary."""
        return {
            "step_index": self.step_index,
            "rule_name": self.rule_name,
            "source_form": self.source_form,
            "target_form": self.target_form,
            "unifier": dict(self.unifier),
            "ast_node_id": self.ast_node_id,
            "span": self.span.to_dict() if self.span is not None else None,
        }


@dataclass(slots=True)
class TermBuildResult:
    """Result of translating a SIPL AST node into a semantic term with derivation steps."""

    term: SemanticTerm
    steps: list[DerivationStep]
    source_program: str | None = None

    def format_unicode(self) -> str:
        """Render the resulting semantic term in course Unicode notation."""
        return self.term.format_unicode()

    def format_latex(self) -> str:
        """Render the resulting semantic term in LaTeX notation."""
        return self.term.format_latex()

    def format_derivation_text(self) -> str:
        """Render the full step-by-step ``sem_*`` replacement trace in Ukrainian."""
        lines: list[str] = []
        if self.source_program is not None:
            lines.append(f"Вихідний текст: {self.source_program}")
        for step in self.steps:
            if step.unifier:
                unif_str = ", ".join(f"{k} ↦ {v}" for k, v in step.unifier.items())
                lines.append(
                    f"Крок {step.step_index} [{step.rule_name}]: "
                    f"{step.source_form} = {step.target_form}  (уніфікатор: [{unif_str}])"
                )
            else:
                lines.append(
                    f"Крок {step.step_index} [{step.rule_name}]: "
                    f"{step.source_form} = {step.target_form}"
                )
        lines.append(f"Отриманий семантичний терм: {self.format_unicode()}")
        return "\n".join(lines)

    def to_dict(self) -> dict[str, Any]:
        """Serialize this build result into a JSON-compatible dictionary."""
        return {
            "source_program": self.source_program,
            "unicode": self.format_unicode(),
            "latex": self.format_latex(),
            "term": self.term.to_dict(),
            "steps": [step.to_dict() for step in self.steps],
        }


def _format_ast_sipl(node: ASTNode) -> str:
    if isinstance(node, Number):
        return str(node.value)
    if isinstance(node, Variable):
        return node.name
    if isinstance(node, ParenAexp):
        return f"({_format_ast_sipl(node.expr)})"
    if isinstance(node, BinaryAexp):
        return f"{_format_ast_sipl(node.left)} {node.op} {_format_ast_sipl(node.right)}"
    if isinstance(node, CompareBexp):
        return f"{_format_ast_sipl(node.left)} {node.op} {_format_ast_sipl(node.right)}"
    if isinstance(node, BinaryBexp):
        sym = "\u2228" if node.op == "or" else node.op
        return f"{_format_ast_sipl(node.left)} {sym} {_format_ast_sipl(node.right)}"
    if isinstance(node, NotBexp):
        return f"\u00ac{_format_ast_sipl(node.operand)}"
    if isinstance(node, ParenBexp):
        return f"({_format_ast_sipl(node.cond)})"
    if isinstance(node, Skip):
        return "skip"
    if isinstance(node, Assign):
        return f"{node.var} := {_format_ast_sipl(node.expr)}"
    if isinstance(node, Seq):
        return f"{_format_ast_sipl(node.left)}; {_format_ast_sipl(node.right)}"
    if isinstance(node, If):
        return (
            f"if {_format_ast_sipl(node.cond)} "
            f"then {_format_ast_sipl(node.then_branch)} "
            f"else {_format_ast_sipl(node.else_branch)}"
        )
    if isinstance(node, While):
        return f"while {_format_ast_sipl(node.cond)} do {_format_ast_sipl(node.body)}"
    if isinstance(node, Block):
        return f"begin {_format_ast_sipl(node.body)} end"
    if isinstance(node, Program):
        return f"begin {_format_ast_sipl(node.body)} end"
    raise SiplSemanticError(f"Unsupported AST node type: {type(node).__name__}")


class _TermBuilder:
    """Recursive ``sem_*`` translator collecting ``DerivationStep`` entries."""

    def __init__(self) -> None:
        self._term_counter = 0
        self._step_counter = 0
        self.steps: list[DerivationStep] = []

    def _next_term_id(self) -> str:
        self._term_counter += 1
        return f"t_{self._term_counter}"

    def _record_step(
        self,
        rule_name: str,
        source_form: str,
        target_form: str,
        unifier: dict[str, str],
        node: ASTNode,
    ) -> None:
        self._step_counter += 1
        self.steps.append(
            DerivationStep(
                step_index=self._step_counter,
                rule_name=rule_name,
                source_form=source_form,
                target_form=target_form,
                unifier=unifier,
                ast_node_id=node.node_id,
                span=node.span,
            )
        )

    def build_program(self, prog: Program) -> TFS:
        body_src = _format_ast_sipl(prog.body)
        prog_src = f"begin {body_src} end"
        self._record_step(
            rule_name="NS_Prog",
            source_form=f"sem_P({prog_src})",
            target_form=f"sem_S({body_src})",
            unifier={"S": body_src},
            node=prog,
        )
        return self.build_stm(prog.body)

    def build_stm(self, stm: Stm) -> TFS:
        if isinstance(stm, Assign):
            expr_src = _format_ast_sipl(stm.expr)
            stm_src = f"{stm.var} := {expr_src}"
            self._record_step(
                rule_name="NS_Stm_As",
                source_form=f"sem_S({stm_src})",
                target_form=f"AS^{stm.var}(sem_A({expr_src}))",
                unifier={"x": stm.var, "a": expr_src},
                node=stm,
            )
            expr_term = self.build_aexp(stm.expr)
            return AssignTerm(
                var=stm.var,
                expr=expr_term,
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        if isinstance(stm, Seq):
            left_src = _format_ast_sipl(stm.left)
            right_src = _format_ast_sipl(stm.right)
            self._record_step(
                rule_name="NS_Stm_Seq",
                source_form=f"sem_S({left_src}; {right_src})",
                target_form=f"sem_S({left_src}) \u00b7 sem_S({right_src})",
                unifier={"S1": left_src, "S2": right_src},
                node=stm,
            )
            left_term = self.build_stm(stm.left)
            right_term = self.build_stm(stm.right)
            return SeqTerm(
                left=left_term,
                right=right_term,
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        if isinstance(stm, If):
            cond_src = _format_ast_sipl(stm.cond)
            then_src = _format_ast_sipl(stm.then_branch)
            else_src = _format_ast_sipl(stm.else_branch)
            self._record_step(
                rule_name="NS_Stm_If",
                source_form=f"sem_S(if {cond_src} then {then_src} else {else_src})",
                target_form=f"IF(sem_B({cond_src}), sem_S({then_src}), sem_S({else_src}))",
                unifier={"b": cond_src, "S1": then_src, "S2": else_src},
                node=stm,
            )
            cond_term = self.build_bexp(stm.cond)
            then_term = self.build_stm(stm.then_branch)
            else_term = self.build_stm(stm.else_branch)
            return IfTerm(
                cond=cond_term,
                then_term=then_term,
                else_term=else_term,
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        if isinstance(stm, While):
            cond_src = _format_ast_sipl(stm.cond)
            body_src = _format_ast_sipl(stm.body)
            self._record_step(
                rule_name="NS_Stm_Wh",
                source_form=f"sem_S(while {cond_src} do {body_src})",
                target_form=f"WH(sem_B({cond_src}), sem_S({body_src}))",
                unifier={"b": cond_src, "S": body_src},
                node=stm,
            )
            cond_term = self.build_bexp(stm.cond)
            body_term = self.build_stm(stm.body)
            return WhileTerm(
                cond=cond_term,
                body=body_term,
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        if isinstance(stm, Block):
            inner_src = _format_ast_sipl(stm.body)
            self._record_step(
                rule_name="NS_Stm_BE",
                source_form=f"sem_S(begin {inner_src} end)",
                target_form=f"(sem_S({inner_src}))",
                unifier={"S": inner_src},
                node=stm,
            )
            inner_term = self.build_stm(stm.body)
            return BlockTerm(
                inner=inner_term,
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        if isinstance(stm, Skip):
            self._record_step(
                rule_name="NS_Stm_skip",
                source_form="sem_S(skip)",
                target_form="id",
                unifier={},
                node=stm,
            )
            return IdTerm(
                term_id=self._next_term_id(),
                ast_node_id=stm.node_id,
                span=stm.span,
            )

        raise _semantic_error(f"Unsupported Stm AST node: {type(stm).__name__}", stm.span)

    def build_aexp(self, expr: Aexp) -> TFA:
        if isinstance(expr, Number):
            num_str = str(expr.value)
            term = ConstNumTerm(
                value=expr.value,
                term_id=self._next_term_id(),
                ast_node_id=expr.node_id,
                span=expr.span,
            )
            self._record_step(
                rule_name="NS_A_Num",
                source_form=f"sem_A({num_str})",
                target_form=term.format_unicode(),
                unifier={"n": num_str},
                node=expr,
            )
            return term

        if isinstance(expr, Variable):
            term_var = DerefTerm(
                var=expr.name,
                term_id=self._next_term_id(),
                ast_node_id=expr.node_id,
                span=expr.span,
            )
            self._record_step(
                rule_name="NS_A_Var",
                source_form=f"sem_A({expr.name})",
                target_form=term_var.format_unicode(),
                unifier={"x": expr.name},
                node=expr,
            )
            return term_var

        if isinstance(expr, BinaryAexp):
            op_info = _AEXP_OP_MAP.get(expr.op)
            if op_info is None:
                raise _semantic_error(f"Unsupported arithmetic operator '{expr.op}'", expr.span)
            op_name, rule_name = op_info
            left_src = _format_ast_sipl(expr.left)
            right_src = _format_ast_sipl(expr.right)
            self._record_step(
                rule_name=rule_name,
                source_form=f"sem_A({left_src} {expr.op} {right_src})",
                target_form=f"S^2({op_name}, sem_A({left_src}), sem_A({right_src}))",
                unifier={"a1": left_src, "a2": right_src},
                node=expr,
            )
            left_term = self.build_aexp(expr.left)
            right_term = self.build_aexp(expr.right)
            return SuperposAexpTerm(
                op_name=op_name,
                args=[left_term, right_term],
                term_id=self._next_term_id(),
                ast_node_id=expr.node_id,
                span=expr.span,
            )

        if isinstance(expr, ParenAexp):
            inner_src = _format_ast_sipl(expr.expr)
            self._record_step(
                rule_name="NS_A_Par",
                source_form=f"sem_A(({inner_src}))",
                target_form=f"sem_A({inner_src})",
                unifier={"a": inner_src},
                node=expr,
            )
            return self.build_aexp(expr.expr)

        raise _semantic_error(f"Unsupported Aexp AST node: {type(expr).__name__}", expr.span)

    def build_bexp(self, cond: Bexp) -> TFB:
        if isinstance(cond, CompareBexp):
            op_info = _CMP_OP_MAP.get(cond.op)
            if op_info is None:
                raise _semantic_error(f"Unsupported comparison operator '{cond.op}'", cond.span)
            op_name, rule_name = op_info
            left_src = _format_ast_sipl(cond.left)
            right_src = _format_ast_sipl(cond.right)
            self._record_step(
                rule_name=rule_name,
                source_form=f"sem_B({left_src} {cond.op} {right_src})",
                target_form=f"S^2({op_name}, sem_A({left_src}), sem_A({right_src}))",
                unifier={"a1": left_src, "a2": right_src},
                node=cond,
            )
            left_a = self.build_aexp(cond.left)
            right_a = self.build_aexp(cond.right)
            return SuperposCmpTerm(
                op_name=op_name,
                left=left_a,
                right=right_a,
                term_id=self._next_term_id(),
                ast_node_id=cond.node_id,
                span=cond.span,
            )

        if isinstance(cond, BinaryBexp):
            op_info = _BOOL_OP_MAP.get(cond.op)
            if op_info is None:
                raise _semantic_error(f"Unsupported boolean operator '{cond.op}'", cond.span)
            op_name, rule_name = op_info
            left_src = _format_ast_sipl(cond.left)
            right_src = _format_ast_sipl(cond.right)
            sym = "\u2228" if cond.op == "or" else cond.op
            self._record_step(
                rule_name=rule_name,
                source_form=f"sem_B({left_src} {sym} {right_src})",
                target_form=f"S^2({op_name}, sem_B({left_src}), sem_B({right_src}))",
                unifier={"b1": left_src, "b2": right_src},
                node=cond,
            )
            left_b = self.build_bexp(cond.left)
            right_b = self.build_bexp(cond.right)
            return SuperposBoolTerm(
                op_name=op_name,
                args=[left_b, right_b],
                term_id=self._next_term_id(),
                ast_node_id=cond.node_id,
                span=cond.span,
            )

        if isinstance(cond, NotBexp):
            inner_src = _format_ast_sipl(cond.operand)
            self._record_step(
                rule_name="NS_B_neg",
                source_form=f"sem_B(\u00ac{inner_src})",
                target_form=f"S^1(neg, sem_B({inner_src}))",
                unifier={"b": inner_src},
                node=cond,
            )
            inner_term = self.build_bexp(cond.operand)
            return SuperposBoolTerm(
                op_name="neg",
                args=[inner_term],
                term_id=self._next_term_id(),
                ast_node_id=cond.node_id,
                span=cond.span,
            )

        if isinstance(cond, ParenBexp):
            inner_src = _format_ast_sipl(cond.cond)
            self._record_step(
                rule_name="NS_B_Par",
                source_form=f"sem_B(({inner_src}))",
                target_form=f"sem_B({inner_src})",
                unifier={"b": inner_src},
                node=cond,
            )
            return self.build_bexp(cond.cond)

        raise _semantic_error(f"Unsupported Bexp AST node: {type(cond).__name__}", cond.span)


def build_stm_term(stm: Stm, *, source_program: str | None = None) -> TermBuildResult:
    """Translate a SIPL statement ``Stm`` into a ``TFS`` semantic term."""
    builder = _TermBuilder()
    term = builder.build_stm(stm)
    return TermBuildResult(
        term=term,
        steps=builder.steps,
        source_program=source_program if source_program is not None else _format_ast_sipl(stm),
    )


def build_aexp_term(expr: Aexp, *, source_program: str | None = None) -> TermBuildResult:
    """Translate a SIPL arithmetic expression ``Aexp`` into a ``TFA`` semantic term."""
    builder = _TermBuilder()
    term = builder.build_aexp(expr)
    return TermBuildResult(
        term=term,
        steps=builder.steps,
        source_program=source_program if source_program is not None else _format_ast_sipl(expr),
    )


def build_bexp_term(cond: Bexp, *, source_program: str | None = None) -> TermBuildResult:
    """Translate a SIPL boolean condition ``Bexp`` into a ``TFB`` semantic term."""
    builder = _TermBuilder()
    term = builder.build_bexp(cond)
    return TermBuildResult(
        term=term,
        steps=builder.steps,
        source_program=source_program if source_program is not None else _format_ast_sipl(cond),
    )


def build_semantic_term(
    program_or_node: Program | Stm | Aexp | Bexp,
    *,
    source_program: str | None = None,
) -> TermBuildResult:
    """Translate a SIPL ``Program``, ``Stm``, ``Aexp``, or ``Bexp`` into a semantic term.

    Applies the replacement rules ``NS_Prog``, ``NS_Stm_*``, ``NS_A_*``, and
    ``NS_B_*`` from Practical Work 2 (p. 15) and records every step in the
    returned ``TermBuildResult``.
    """
    if isinstance(program_or_node, Program):
        builder = _TermBuilder()
        term = builder.build_program(program_or_node)
        src = (
            source_program
            if source_program is not None
            else _format_ast_sipl(program_or_node)
        )
        return TermBuildResult(term=term, steps=builder.steps, source_program=src)
    if isinstance(program_or_node, Stm):
        return build_stm_term(program_or_node, source_program=source_program)
    if isinstance(program_or_node, Aexp):
        return build_aexp_term(program_or_node, source_program=source_program)
    if isinstance(program_or_node, Bexp):
        return build_bexp_term(program_or_node, source_program=source_program)
    raise SiplSemanticError(
        f"Expected Program, Stm, Aexp, or Bexp, got {type(program_or_node).__name__}"
    )
