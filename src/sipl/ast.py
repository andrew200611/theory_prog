"""Typed Abstract Syntax Tree (AST) and Concrete Parse Tree data models for SIPL."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from sipl.diagnostics import SourceSpan


def _serialize_value(value: Any) -> Any:
    if isinstance(value, ASTNode):
        return value.to_dict()
    if isinstance(value, SourceSpan):
        return value.to_dict()
    if isinstance(value, list):
        return [_serialize_value(item) for item in value]
    return value


@dataclass(frozen=True, slots=True)
class ASTNode:
    """Base class for all typed SIPL AST nodes."""

    span: SourceSpan
    node_id: str

    def to_dict(self) -> dict[str, Any]:
        """Serialize this AST node and its children into a JSON-compatible dictionary."""
        result: dict[str, Any] = {
            "kind": self.__class__.__name__,
            "node_id": self.node_id,
            "span": self.span.to_dict(),
        }
        for cls in self.__class__.__mro__:
            annotations = getattr(cls, "__annotations__", {})
            for attr in annotations:
                if attr in ("span", "node_id") or attr.startswith("_"):
                    continue
                val = getattr(self, attr)
                if val is not None:
                    result[attr] = _serialize_value(val)
        return result


@dataclass(frozen=True, slots=True)
class Aexp(ASTNode):
    """Base class for SIPL arithmetic expressions (``Aexp``)."""


@dataclass(frozen=True, slots=True)
class Number(Aexp):
    """Integer literal (``NA1 -> NN``)."""

    value: int


@dataclass(frozen=True, slots=True)
class Variable(Aexp):
    """Variable reference in an expression (``NA2 -> NV``)."""

    name: str


@dataclass(frozen=True, slots=True)
class BinaryAexp(Aexp):
    """Binary arithmetic operation (``+``, ``-``, ``*``, ``div``, ``mod``)."""

    op: str
    left: Aexp
    right: Aexp


@dataclass(frozen=True, slots=True)
class ParenAexp(Aexp):
    """Parenthesized arithmetic expression ``(a)`` (``NA6``)."""

    expr: Aexp


@dataclass(frozen=True, slots=True)
class Bexp(ASTNode):
    """Base class for SIPL boolean conditions (``Bexp``)."""


@dataclass(frozen=True, slots=True)
class CompareBexp(Bexp):
    """Comparison between two arithmetic expressions (``=``, ``>``, ``>=``, ``<``, ``<=``)."""

    op: str
    left: Aexp
    right: Aexp


@dataclass(frozen=True, slots=True)
class BinaryBexp(Bexp):
    """Binary boolean combinator (``or``, ``and``)."""

    op: str
    left: Bexp
    right: Bexp


@dataclass(frozen=True, slots=True)
class NotBexp(Bexp):
    """Logical negation ``¬ b`` / ``not b`` (``NB4``)."""

    operand: Bexp


@dataclass(frozen=True, slots=True)
class ParenBexp(Bexp):
    """Parenthesized boolean condition ``(b)`` (``NB5``)."""

    cond: Bexp


@dataclass(frozen=True, slots=True)
class Stm(ASTNode):
    """Base class for SIPL statements (``Stm``)."""


@dataclass(frozen=True, slots=True)
class Assign(Stm):
    """Variable assignment ``x := a`` (``NS1``)."""

    var: str
    expr: Aexp
    var_span: SourceSpan | None = None


@dataclass(frozen=True, slots=True)
class Seq(Stm):
    """Sequential composition ``S1 ; S2`` (``NS2``)."""

    left: Stm
    right: Stm


@dataclass(frozen=True, slots=True)
class If(Stm):
    """Conditional statement ``if b then S1 else S2`` (``NS3``)."""

    cond: Bexp
    then_branch: Stm
    else_branch: Stm


@dataclass(frozen=True, slots=True)
class While(Stm):
    """While loop ``while b do S`` (``NS4``)."""

    cond: Bexp
    body: Stm


@dataclass(frozen=True, slots=True)
class Block(Stm):
    """Compound block ``begin S end`` (``NS5``)."""

    body: Stm


@dataclass(frozen=True, slots=True)
class Skip(Stm):
    """No-op statement ``skip`` (``NS6``)."""


@dataclass(frozen=True, slots=True)
class Program(ASTNode):
    """Top-level SIPL program ``begin S end`` (``NP1``)."""

    body: Stm


@dataclass(slots=True)
class ParseTreeNode:
    """Node in the concrete SIPL derivation tree (Practice 1, Fig. 1 & Fig. 2)."""

    label: str
    category: str | None
    rule_name: str | None
    span: SourceSpan
    node_id: str
    children: list[ParseTreeNode] = field(default_factory=list)
    is_terminal: bool = False
    token_text: str | None = None
    leaf_index: int | None = None
    ast_node_id: str | None = None

    def leaves(self) -> list[ParseTreeNode]:
        """Return all terminal leaves in left-to-right depth-first order."""
        if self.is_terminal:
            return [self]
        result: list[ParseTreeNode] = []
        for child in self.children:
            result.extend(child.leaves())
        return result

    def crown_tokens(self) -> list[str]:
        """Return the ordered list of terminal token strings along the tree crown."""
        return [
            leaf.token_text if leaf.token_text is not None else leaf.label
            for leaf in self.leaves()
        ]

    def numbered_crown(self) -> str:
        """Return the numbered crown string ``1 tok1 2 tok2 ...`` (Practice 1 p. 10)."""
        parts: list[str] = []
        for idx, leaf in enumerate(self.leaves(), start=1):
            leaf_no = leaf.leaf_index if leaf.leaf_index is not None else idx
            text = leaf.token_text if leaf.token_text is not None else leaf.label
            parts.append(f"{leaf_no} {text}")
        return " ".join(parts)

    def to_dict(self) -> dict[str, Any]:
        """Serialize this parse tree node recursively to a JSON-compatible dictionary."""
        return {
            "node_id": self.node_id,
            "label": self.label,
            "category": self.category,
            "rule_name": self.rule_name,
            "is_terminal": self.is_terminal,
            "token_text": self.token_text,
            "leaf_index": self.leaf_index,
            "ast_node_id": self.ast_node_id,
            "span": self.span.to_dict(),
            "children": [child.to_dict() for child in self.children],
        }
