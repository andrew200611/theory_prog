"""Symbolic expression AST, algebraic canonical simplifier, parser, and evaluator."""

from __future__ import annotations

import math
import re
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

from sipl.ast import (
    Aexp,
    Bexp,
    BinaryAexp,
    BinaryBexp,
    CompareBexp,
    NotBexp,
    Number,
    ParenAexp,
    ParenBexp,
    Variable,
)
from sipl.diagnostics import SiplSemanticError


@dataclass(frozen=True, slots=True)
class SymExpr:
    """Base class for symbolic arithmetic expressions."""

    def format_unicode(self) -> str:
        raise NotImplementedError

    def format_latex(self) -> str:
        raise NotImplementedError

    def free_vars(self) -> set[str]:
        raise NotImplementedError

    def to_dict(self) -> dict[str, Any]:
        raise NotImplementedError

    def __str__(self) -> str:
        return self.format_unicode()


@dataclass(frozen=True, slots=True)
class SymConst(SymExpr):
    """Integer constant."""

    value: int

    def format_unicode(self) -> str:
        if self.value < 0:
            return f"\u2212{-self.value}"
        return str(self.value)

    def format_latex(self) -> str:
        return str(self.value)

    def free_vars(self) -> set[str]:
        return set()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymConst", "value": self.value}


@dataclass(frozen=True, slots=True)
class SymVar(SymExpr):
    """Symbolic variable."""

    name: str

    def format_unicode(self) -> str:
        return self.name

    def format_latex(self) -> str:
        return _latex_ident(self.name)

    def free_vars(self) -> set[str]:
        return {self.name}

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymVar", "name": self.name}


@dataclass(frozen=True, slots=True)
class SymAdd(SymExpr):
    """Symbolic addition ``left + right``."""

    left: SymExpr
    right: SymExpr

    def format_unicode(self) -> str:
        left_s = _wrap_unicode(self.left, _PREC_ADD, is_right=False)
        right_s = _wrap_unicode(self.right, _PREC_ADD, is_right=True)
        return f"{left_s} + {right_s}"

    def format_latex(self) -> str:
        left_s = _wrap_latex(self.left, _PREC_ADD, is_right=False)
        right_s = _wrap_latex(self.right, _PREC_ADD, is_right=True)
        return f"{left_s} + {right_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymAdd", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymSub(SymExpr):
    """Symbolic subtraction ``left - right``."""

    left: SymExpr
    right: SymExpr

    def format_unicode(self) -> str:
        if isinstance(self.left, SymConst) and self.left.value == 0:
            inner = _wrap_unicode(self.right, _PREC_UNARY, is_right=True)
            return f"\u2212{inner}"
        left_s = _wrap_unicode(self.left, _PREC_ADD, is_right=False)
        right_s = _wrap_unicode(self.right, _PREC_SUB_RIGHT, is_right=True)
        return f"{left_s} \u2212 {right_s}"

    def format_latex(self) -> str:
        if isinstance(self.left, SymConst) and self.left.value == 0:
            inner = _wrap_latex(self.right, _PREC_UNARY, is_right=True)
            return f"-{inner}"
        left_s = _wrap_latex(self.left, _PREC_ADD, is_right=False)
        right_s = _wrap_latex(self.right, _PREC_SUB_RIGHT, is_right=True)
        return f"{left_s} - {right_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymSub", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymMul(SymExpr):
    """Symbolic multiplication ``left * right``."""

    left: SymExpr
    right: SymExpr

    def format_unicode(self) -> str:
        if isinstance(self.left, SymConst) and self.left.value == -1:
            inner = _wrap_unicode(self.right, _PREC_UNARY, is_right=True)
            return f"\u2212{inner}"
        left_s = _wrap_unicode(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_unicode(self.right, _PREC_MUL, is_right=True)
        if _can_juxtapose(self.left, self.right):
            return f"{left_s}{right_s}"
        return f"{left_s}\u00b7{right_s}"

    def format_latex(self) -> str:
        if isinstance(self.left, SymConst) and self.left.value == -1:
            inner = _wrap_latex(self.right, _PREC_UNARY, is_right=True)
            return f"-{inner}"
        left_s = _wrap_latex(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_latex(self.right, _PREC_MUL, is_right=True)
        if _can_juxtapose(self.left, self.right):
            return f"{left_s}{right_s}"
        return rf"{left_s} \cdot {right_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymMul", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymDiv(SymExpr):
    """Symbolic integer division ``left div right``."""

    left: SymExpr
    right: SymExpr

    def format_unicode(self) -> str:
        left_s = _wrap_unicode(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_unicode(self.right, _PREC_DIV_RIGHT, is_right=True)
        return f"{left_s} div {right_s}"

    def format_latex(self) -> str:
        left_s = _wrap_latex(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_latex(self.right, _PREC_DIV_RIGHT, is_right=True)
        return rf"{left_s} \operatorname{{div}} {right_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymDiv", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymMod(SymExpr):
    """Symbolic integer modulo ``left mod right``."""

    left: SymExpr
    right: SymExpr

    def format_unicode(self) -> str:
        left_s = _wrap_unicode(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_unicode(self.right, _PREC_DIV_RIGHT, is_right=True)
        return f"{left_s} mod {right_s}"

    def format_latex(self) -> str:
        left_s = _wrap_latex(self.left, _PREC_MUL, is_right=False)
        right_s = _wrap_latex(self.right, _PREC_DIV_RIGHT, is_right=True)
        return rf"{left_s} \bmod {right_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymMod", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymPow(SymExpr):
    """Symbolic exponentiation ``base ** exp``."""

    base: SymExpr
    exp: SymExpr

    def format_unicode(self) -> str:
        base_s = _wrap_unicode(self.base, _PREC_POW_BASE, is_right=False)
        if isinstance(self.exp, SymConst) and self.exp.value >= 0:
            exp_s = self.exp.format_unicode()
        elif isinstance(self.exp, SymVar):
            exp_s = self.exp.format_unicode()
        else:
            exp_s = f"({self.exp.format_unicode()})"
        return f"{base_s}^{exp_s}"

    def format_latex(self) -> str:
        base_s = _wrap_latex(self.base, _PREC_POW_BASE, is_right=False)
        return f"{{{base_s}}}^{{{self.exp.format_latex()}}}"

    def free_vars(self) -> set[str]:
        return self.base.free_vars() | self.exp.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymPow", "base": self.base.to_dict(), "exp": self.exp.to_dict()}


@dataclass(frozen=True, slots=True)
class SymFact(SymExpr):
    """Symbolic factorial ``arg!``."""

    arg: SymExpr

    def format_unicode(self) -> str:
        if isinstance(self.arg, (SymVar, SymConst)) and not (
            isinstance(self.arg, SymConst) and self.arg.value < 0
        ):
            return f"{self.arg.format_unicode()}!"
        return f"({self.arg.format_unicode()})!"

    def format_latex(self) -> str:
        if isinstance(self.arg, (SymVar, SymConst)) and not (
            isinstance(self.arg, SymConst) and self.arg.value < 0
        ):
            return f"{self.arg.format_latex()}!"
        return f"({self.arg.format_latex()})!"

    def free_vars(self) -> set[str]:
        return self.arg.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymFact", "arg": self.arg.to_dict()}


@dataclass(frozen=True, slots=True)
class SymIf(SymExpr):
    """Symbolic conditional expression ``if cond then then_e else else_e``."""

    cond: SymBool
    then_e: SymExpr
    else_e: SymExpr

    def format_unicode(self) -> str:
        return (
            f"(if {self.cond.format_unicode()} "
            f"then {self.then_e.format_unicode()} "
            f"else {self.else_e.format_unicode()})"
        )

    def format_latex(self) -> str:
        return (
            rf"\begin{{cases}} {self.then_e.format_latex()}, & \text{{якщо }} "
            rf"{self.cond.format_latex()} \\ "
            rf"{self.else_e.format_latex()}, & \text{{інакше}} \end{{cases}}"
        )

    def free_vars(self) -> set[str]:
        return self.cond.free_vars() | self.then_e.free_vars() | self.else_e.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {
            "kind": "SymIf",
            "cond": self.cond.to_dict(),
            "then_e": self.then_e.to_dict(),
            "else_e": self.else_e.to_dict(),
        }


@dataclass(frozen=True, slots=True)
class SymBool:
    """Base class for symbolic boolean predicates."""

    def format_unicode(self) -> str:
        raise NotImplementedError

    def format_latex(self) -> str:
        raise NotImplementedError

    def free_vars(self) -> set[str]:
        raise NotImplementedError

    def to_dict(self) -> dict[str, Any]:
        raise NotImplementedError

    def __str__(self) -> str:
        return self.format_unicode()


@dataclass(frozen=True, slots=True)
class SymBoolConst(SymBool):
    """Constant boolean predicate."""

    value: bool

    def format_unicode(self) -> str:
        return "true" if self.value else "false"

    def format_latex(self) -> str:
        return r"\mathrm{true}" if self.value else r"\mathrm{false}"

    def free_vars(self) -> set[str]:
        return set()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymBoolConst", "value": self.value}


@dataclass(frozen=True, slots=True)
class SymCmp(SymBool):
    """Symbolic comparison predicate ``left op right``."""

    op: str
    left: SymExpr
    right: SymExpr

    def __post_init__(self) -> None:
        if self.op == "==":
            object.__setattr__(self, "op", "=")
        elif self.op not in ("=", ">", ">=", "<", "<=", "!="):
            raise SiplSemanticError(f"Unsupported comparison operator: {self.op!r}")

    def format_unicode(self) -> str:
        op_map = {
            "=": "=",
            ">": ">",
            ">=": "\u2265",
            "<": "<",
            "<=": "\u2264",
            "!=": "\u2260",
        }
        return f"{self.left.format_unicode()} {op_map[self.op]} {self.right.format_unicode()}"

    def format_latex(self) -> str:
        op_map = {
            "=": "=",
            ">": ">",
            ">=": r"\ge",
            "<": "<",
            "<=": r"\le",
            "!=": r"\ne",
        }
        return f"{self.left.format_latex()} {op_map[self.op]} {self.right.format_latex()}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {
            "kind": "SymCmp",
            "op": self.op,
            "left": self.left.to_dict(),
            "right": self.right.to_dict(),
        }


@dataclass(frozen=True, slots=True)
class SymAnd(SymBool):
    """Logical conjunction ``left ∧ right``."""

    left: SymBool
    right: SymBool

    def format_unicode(self) -> str:
        l_s = (
            f"({self.left.format_unicode()})"
            if isinstance(self.left, SymOr)
            else self.left.format_unicode()
        )
        r_s = (
            f"({self.right.format_unicode()})"
            if isinstance(self.right, SymOr)
            else self.right.format_unicode()
        )
        return f"{l_s} \u2227 {r_s}"

    def format_latex(self) -> str:
        l_s = (
            f"({self.left.format_latex()})"
            if isinstance(self.left, SymOr)
            else self.left.format_latex()
        )
        r_s = (
            f"({self.right.format_latex()})"
            if isinstance(self.right, SymOr)
            else self.right.format_latex()
        )
        return rf"{l_s} \land {r_s}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymAnd", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymOr(SymBool):
    """Logical disjunction ``left ∨ right``."""

    left: SymBool
    right: SymBool

    def format_unicode(self) -> str:
        return f"{self.left.format_unicode()} \u2228 {self.right.format_unicode()}"

    def format_latex(self) -> str:
        return rf"{self.left.format_latex()} \lor {self.right.format_latex()}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymOr", "left": self.left.to_dict(), "right": self.right.to_dict()}


@dataclass(frozen=True, slots=True)
class SymNot(SymBool):
    """Logical negation ``¬operand``."""

    operand: SymBool

    def format_unicode(self) -> str:
        if isinstance(self.operand, (SymBoolConst, SymNot)):
            return f"\u00ac{self.operand.format_unicode()}"
        return f"\u00ac({self.operand.format_unicode()})"

    def format_latex(self) -> str:
        if isinstance(self.operand, (SymBoolConst, SymNot)):
            return rf"\neg {self.operand.format_latex()}"
        return rf"\neg ({self.operand.format_latex()})"

    def free_vars(self) -> set[str]:
        return self.operand.free_vars()

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "SymNot", "operand": self.operand.to_dict()}


@dataclass(frozen=True, slots=True)
class SymState:
    """Immutable-style mapping from SIPL variable names to symbolic expressions."""

    mapping: dict[str, SymExpr]

    def __post_init__(self) -> None:
        object.__setattr__(self, "mapping", dict(self.mapping))

    def get(self, var: str, default: SymExpr | None = None) -> SymExpr | None:
        return self.mapping.get(var, default)

    def __getitem__(self, var: str) -> SymExpr:
        if var not in self.mapping:
            raise SiplSemanticError(f"Undefined symbolic variable '{var}'")
        return self.mapping[var]

    def __contains__(self, var: object) -> bool:
        return var in self.mapping

    def keys(self) -> list[str]:
        return list(self.mapping.keys())

    def values(self) -> list[SymExpr]:
        return list(self.mapping.values())

    def items(self) -> list[tuple[str, SymExpr]]:
        return list(self.mapping.items())

    def overlay(self, updates: Mapping[str, SymExpr]) -> SymState:
        merged = dict(self.mapping)
        merged.update(updates)
        return SymState(merged)

    def format_unicode(self) -> str:
        inner = ", ".join(f"{k} \u21a6 {v.format_unicode()}" for k, v in self.mapping.items())
        return f"[{inner}]"

    def format_latex(self) -> str:
        inner = ", ".join(
            rf"{_latex_ident(k)} \mapsto {v.format_latex()}" for k, v in self.mapping.items()
        )
        return f"[{inner}]"

    def to_dict(self) -> dict[str, str]:
        return {k: v.format_unicode() for k, v in self.mapping.items()}

    def __str__(self) -> str:
        return self.format_unicode()


_PREC_IF = 1
_PREC_ADD = 2
_PREC_SUB_RIGHT = 3
_PREC_MUL = 4
_PREC_DIV_RIGHT = 5
_PREC_UNARY = 6
_PREC_POW_BASE = 7
_PREC_ATOM = 8


def _expr_prec(expr: SymExpr) -> int:
    if isinstance(expr, SymIf):
        return _PREC_IF
    if isinstance(expr, (SymAdd, SymSub)):
        if isinstance(expr, SymSub) and isinstance(expr.left, SymConst) and expr.left.value == 0:
            return _PREC_UNARY
        return _PREC_ADD
    if isinstance(expr, (SymMul, SymDiv, SymMod)):
        if isinstance(expr, SymMul) and isinstance(expr.left, SymConst) and expr.left.value == -1:
            return _PREC_UNARY
        return _PREC_MUL
    if isinstance(expr, SymPow):
        return _PREC_POW_BASE
    return _PREC_ATOM


def _wrap_unicode(expr: SymExpr, min_prec: int, *, is_right: bool) -> str:
    prec = _expr_prec(expr)
    text = expr.format_unicode()
    if prec < min_prec:
        return f"({text})"
    if isinstance(expr, (SymDiv, SymMod)) and min_prec >= _PREC_MUL:
        return f"({text})"
    if not is_right and isinstance(expr, SymPow) and min_prec == _PREC_POW_BASE:
        return f"({text})"
    if is_right and isinstance(expr, SymConst) and expr.value < 0 and min_prec >= _PREC_ADD:
        return f"({text})"
    return text


def _wrap_latex(expr: SymExpr, min_prec: int, *, is_right: bool) -> str:
    prec = _expr_prec(expr)
    text = expr.format_latex()
    if prec < min_prec:
        return f"({text})"
    if isinstance(expr, (SymDiv, SymMod)) and min_prec >= _PREC_MUL:
        return f"({text})"
    if not is_right and isinstance(expr, SymPow) and min_prec == _PREC_POW_BASE:
        return f"({text})"
    if is_right and isinstance(expr, SymConst) and expr.value < 0 and min_prec >= _PREC_ADD:
        return f"({text})"
    return text


def _can_juxtapose(left: SymExpr, right: SymExpr) -> bool:
    """Decide if ``left * right`` can be written cleanly without an explicit ``·``."""
    right_is_simple_var = isinstance(right, SymVar) and len(right.name) == 1
    right_is_simple_pow = (
        isinstance(right, SymPow) and isinstance(right.base, SymVar) and len(right.base.name) == 1
    )
    if not (right_is_simple_var or right_is_simple_pow):
        return False
    if isinstance(left, SymConst):
        return left.value not in (0, 1, -1)
    if isinstance(left, SymVar):
        return len(left.name) == 1
    if isinstance(left, (SymAdd, SymSub)):
        return True
    if isinstance(left, SymMul):
        return _can_juxtapose(left.right, right)
    return False


def _latex_ident(name: str) -> str:
    if "_" in name:
        base, sub = name.split("_", 1)
        return f"{base}_{{{sub}}}"
    match = re.fullmatch(r"([A-Za-z]+)(\d+)", name)
    if match:
        return f"{match.group(1)}_{{{match.group(2)}}}"
    return name


def aexp_to_sym(expr: Aexp) -> SymExpr:
    """Convert a SIPL ``Aexp`` AST node into a ``SymExpr``."""
    if isinstance(expr, Number):
        return SymConst(expr.value)
    if isinstance(expr, Variable):
        return SymVar(expr.name)
    if isinstance(expr, ParenAexp):
        return aexp_to_sym(expr.expr)
    if isinstance(expr, BinaryAexp):
        left = aexp_to_sym(expr.left)
        right = aexp_to_sym(expr.right)
        if expr.op == "+":
            return SymAdd(left, right)
        if expr.op == "-":
            return SymSub(left, right)
        if expr.op == "*":
            return SymMul(left, right)
        if expr.op == "div":
            return SymDiv(left, right)
        if expr.op == "mod":
            return SymMod(left, right)
        raise SiplSemanticError(f"Unsupported arithmetic operator in AST: {expr.op!r}")
    raise SiplSemanticError(f"Unsupported Aexp node: {type(expr).__name__}")


def bexp_to_sym(cond: Bexp) -> SymBool:
    """Convert a SIPL ``Bexp`` AST node into a ``SymBool``."""
    if isinstance(cond, CompareBexp):
        return SymCmp(cond.op, aexp_to_sym(cond.left), aexp_to_sym(cond.right))
    if isinstance(cond, NotBexp):
        return SymNot(bexp_to_sym(cond.operand))
    if isinstance(cond, ParenBexp):
        return bexp_to_sym(cond.cond)
    if isinstance(cond, BinaryBexp):
        left = bexp_to_sym(cond.left)
        right = bexp_to_sym(cond.right)
        if cond.op == "and":
            return SymAnd(left, right)
        if cond.op == "or":
            return SymOr(left, right)
        raise SiplSemanticError(f"Unsupported boolean operator in AST: {cond.op!r}")
    raise SiplSemanticError(f"Unsupported Bexp node: {type(cond).__name__}")


_SYM_TOKEN_SPECS: list[tuple[str, str]] = [
    ("WS", r"\s+"),
    ("POW", r"\*\*|\^"),
    ("FDIV", r"//"),
    ("GE", r">=|\u2265"),
    ("LE", r"<=|\u2264"),
    ("NE", r"!=|\u2260"),
    ("EQ2", r"=="),
    ("EQ", r"="),
    ("GT", r">"),
    ("LT", r"<"),
    ("OR_SYM", r"\|\||\u2228"),
    ("AND_SYM", r"&&|\u2227"),
    ("NOT_SYM", r"\u00ac"),
    ("BANG", r"!"),
    ("PLUS", r"\+"),
    ("MINUS", r"[-\u2013\u2212]"),
    ("MUL", r"[*\u00b7]"),
    ("SLASH", r"/"),
    ("MOD_SYM", r"%"),
    ("LPAREN", r"\("),
    ("RPAREN", r"\)"),
    ("NUM", r"\d+"),
    ("IDENT", r"[A-Za-z_][A-Za-z0-9_]*"),
]
_SYM_TOKEN_RE = re.compile("|".join(f"(?P<{name}>{pat})" for name, pat in _SYM_TOKEN_SPECS))

_KW_MAP: dict[str, str] = {
    "div": "DIV",
    "mod": "MOD",
    "and": "AND",
    "or": "OR",
    "not": "NOT",
    "true": "TRUE",
    "false": "FALSE",
    "if": "IF",
    "then": "THEN",
    "else": "ELSE",
}


@dataclass(frozen=True, slots=True)
class _SymTok:
    kind: str
    value: str
    pos: int


def _tokenize_sym(text: str) -> list[_SymTok]:
    tokens: list[_SymTok] = []
    pos = 0
    while pos < len(text):
        match = _SYM_TOKEN_RE.match(text, pos)
        if match is None:
            raise SiplSemanticError(
                f"Unexpected character {text[pos]!r} at offset {pos} "
                f"in symbolic expression {text!r}"
            )
        kind = match.lastgroup
        assert kind is not None
        val = match.group(kind)
        pos = match.end()
        if kind == "WS":
            continue
        if kind == "IDENT":
            lowered = val.lower()
            if lowered in _KW_MAP:
                kind = _KW_MAP[lowered]
        elif kind == "OR_SYM":
            kind = "OR"
        elif kind == "AND_SYM":
            kind = "AND"
        elif kind == "NOT_SYM":
            kind = "NOT"
        elif kind == "FDIV":
            kind = "DIV"
        elif kind == "MOD_SYM":
            kind = "MOD"
        tokens.append(_SymTok(kind, val, match.start()))
    return tokens


_CMP_KINDS: dict[str, str] = {
    "EQ": "=",
    "EQ2": "=",
    "GT": ">",
    "GE": ">=",
    "LT": "<",
    "LE": "<=",
    "NE": "!=",
}


class _SymParser:
    def __init__(self, tokens: list[_SymTok], source: str) -> None:
        self.tokens = tokens
        self.source = source
        self.pos = 0

    def _peek(self, offset: int = 0) -> _SymTok | None:
        idx = self.pos + offset
        return self.tokens[idx] if idx < len(self.tokens) else None

    def _advance(self) -> _SymTok:
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def _expect(self, kind: str, desc: str) -> _SymTok:
        tok = self._peek()
        if tok is None or tok.kind != kind:
            found = tok.value if tok else "EOF"
            raise SiplSemanticError(
                f"Expected {desc}, found {found!r} in symbolic expression {self.source!r}"
            )
        return self._advance()

    def parse_expr_all(self) -> SymExpr:
        if not self.tokens:
            raise SiplSemanticError("Empty symbolic expression")
        expr = self.parse_expr()
        if self._peek() is not None:
            extra = self._peek()
            assert extra is not None
            raise SiplSemanticError(
                f"Unexpected trailing token {extra.value!r} in symbolic expression {self.source!r}"
            )
        return expr

    def parse_bool_all(self) -> SymBool:
        if not self.tokens:
            raise SiplSemanticError("Empty symbolic boolean predicate")
        pred = self.parse_bool()
        if self._peek() is not None:
            extra = self._peek()
            assert extra is not None
            raise SiplSemanticError(
                f"Unexpected trailing token {extra.value!r} in symbolic predicate {self.source!r}"
            )
        return pred

    def parse_expr(self) -> SymExpr:
        tok = self._peek()
        if tok is not None and tok.kind == "IF":
            self._advance()
            cond = self.parse_bool()
            self._expect("THEN", "'then'")
            then_e = self.parse_expr()
            self._expect("ELSE", "'else'")
            else_e = self.parse_expr()
            return SymIf(cond, then_e, else_e)
        return self._parse_add()

    def _parse_add(self) -> SymExpr:
        left = self._parse_mul()
        while (tok := self._peek()) is not None and tok.kind in ("PLUS", "MINUS"):
            self._advance()
            right = self._parse_mul()
            left = SymAdd(left, right) if tok.kind == "PLUS" else SymSub(left, right)
        return left

    def _parse_mul(self) -> SymExpr:
        left = self._parse_unary()
        while (tok := self._peek()) is not None and tok.kind in ("MUL", "DIV", "MOD", "SLASH"):
            self._advance()
            right = self._parse_unary()
            if tok.kind == "MUL":
                left = SymMul(left, right)
            elif tok.kind in ("DIV", "SLASH"):
                left = SymDiv(left, right)
            else:
                left = SymMod(left, right)
        return left

    def _parse_unary(self) -> SymExpr:
        tok = self._peek()
        if tok is not None and tok.kind == "MINUS":
            self._advance()
            nxt = self._peek()
            if nxt is not None and nxt.kind == "NUM":
                after = self._peek(1)
                if after is None or after.kind not in ("POW", "BANG"):
                    self._advance()
                    return SymConst(-int(nxt.value))
            operand = self._parse_unary()
            if isinstance(operand, SymConst):
                return SymConst(-operand.value)
            return SymSub(SymConst(0), operand)
        if tok is not None and tok.kind == "PLUS":
            self._advance()
            return self._parse_unary()
        return self._parse_pow()

    def _parse_pow(self) -> SymExpr:
        base = self._parse_postfix()
        tok = self._peek()
        if tok is not None and tok.kind == "POW":
            self._advance()
            exp = self._parse_unary()
            return SymPow(base, exp)
        return base

    def _parse_postfix(self) -> SymExpr:
        expr = self._parse_atom()
        while (tok := self._peek()) is not None and tok.kind == "BANG":
            self._advance()
            expr = SymFact(expr)
        return expr

    def _parse_atom(self) -> SymExpr:
        tok = self._peek()
        if tok is None:
            raise SiplSemanticError(f"Unexpected end of symbolic expression {self.source!r}")
        if tok.kind == "NUM":
            self._advance()
            return SymConst(int(tok.value))
        if tok.kind == "IDENT":
            self._advance()
            return SymVar(tok.value)
        if tok.kind == "LPAREN":
            self._advance()
            inner = self.parse_expr()
            self._expect("RPAREN", "')'")
            return inner
        raise SiplSemanticError(
            f"Expected symbolic expression atom, found {tok.value!r} in {self.source!r}"
        )

    def parse_bool(self) -> SymBool:
        return self._parse_or()

    def _parse_or(self) -> SymBool:
        left = self._parse_and()
        while (tok := self._peek()) is not None and tok.kind == "OR":
            self._advance()
            right = self._parse_and()
            left = SymOr(left, right)
        return left

    def _parse_and(self) -> SymBool:
        left = self._parse_not()
        while (tok := self._peek()) is not None and tok.kind == "AND":
            self._advance()
            right = self._parse_not()
            left = SymAnd(left, right)
        return left

    def _parse_not(self) -> SymBool:
        tok = self._peek()
        if tok is not None and tok.kind in ("NOT", "BANG"):
            self._advance()
            return SymNot(self._parse_not())
        return self._parse_bool_atom()

    def _paren_is_bool(self) -> bool:
        depth = 0
        idx = self.pos
        while idx < len(self.tokens):
            k = self.tokens[idx].kind
            if k == "LPAREN":
                depth += 1
            elif k == "RPAREN":
                depth -= 1
                if depth == 0:
                    nxt = self.tokens[idx + 1] if idx + 1 < len(self.tokens) else None
                    if nxt is not None and nxt.kind in _CMP_KINDS:
                        return False
                    return False
            elif k in _CMP_KINDS or k in ("AND", "OR", "NOT", "TRUE", "FALSE"):
                return True
            idx += 1
        return False

    def _parse_bool_atom(self) -> SymBool:
        tok = self._peek()
        if tok is None:
            raise SiplSemanticError(f"Unexpected end of symbolic predicate {self.source!r}")
        if tok.kind == "TRUE":
            self._advance()
            return SymBoolConst(True)
        if tok.kind == "FALSE":
            self._advance()
            return SymBoolConst(False)
        if tok.kind == "LPAREN" and self._paren_is_bool():
            self._advance()
            inner = self.parse_bool()
            self._expect("RPAREN", "')'")
            return inner
        left = self.parse_expr()
        cmp_tok = self._peek()
        if cmp_tok is None or cmp_tok.kind not in _CMP_KINDS:
            found = cmp_tok.value if cmp_tok else "EOF"
            raise SiplSemanticError(
                f"Expected comparison operator, found {found!r} in {self.source!r}"
            )
        self._advance()
        right = self.parse_expr()
        return SymCmp(_CMP_KINDS[cmp_tok.kind], left, right)


def parse_sym_expr(text: str) -> SymExpr:
    """Parse a textual arithmetic expression into ``SymExpr``."""
    tokens = _tokenize_sym(text)
    return _SymParser(tokens, text).parse_expr_all()


def parse_sym_bool(text: str) -> SymBool:
    """Parse a textual boolean predicate into ``SymBool``."""
    tokens = _tokenize_sym(text)
    return _SymParser(tokens, text).parse_bool_all()


def subst(expr: SymExpr, env: Mapping[str, SymExpr]) -> SymExpr:
    """Substitute variables in ``expr`` according to ``env``."""
    if isinstance(expr, SymConst):
        return expr
    if isinstance(expr, SymVar):
        return env.get(expr.name, expr)
    if isinstance(expr, SymAdd):
        return SymAdd(subst(expr.left, env), subst(expr.right, env))
    if isinstance(expr, SymSub):
        return SymSub(subst(expr.left, env), subst(expr.right, env))
    if isinstance(expr, SymMul):
        return SymMul(subst(expr.left, env), subst(expr.right, env))
    if isinstance(expr, SymDiv):
        return SymDiv(subst(expr.left, env), subst(expr.right, env))
    if isinstance(expr, SymMod):
        return SymMod(subst(expr.left, env), subst(expr.right, env))
    if isinstance(expr, SymPow):
        return SymPow(subst(expr.base, env), subst(expr.exp, env))
    if isinstance(expr, SymFact):
        return SymFact(subst(expr.arg, env))
    if isinstance(expr, SymIf):
        return SymIf(
            subst_bool(expr.cond, env),
            subst(expr.then_e, env),
            subst(expr.else_e, env),
        )
    raise SiplSemanticError(f"Unknown SymExpr node: {type(expr).__name__}")


subst_expr = subst


def subst_bool(pred: SymBool, env: Mapping[str, SymExpr]) -> SymBool:
    """Substitute variables in ``pred`` according to ``env``."""
    if isinstance(pred, SymBoolConst):
        return pred
    if isinstance(pred, SymCmp):
        return SymCmp(pred.op, subst(pred.left, env), subst(pred.right, env))
    if isinstance(pred, SymAnd):
        return SymAnd(subst_bool(pred.left, env), subst_bool(pred.right, env))
    if isinstance(pred, SymOr):
        return SymOr(subst_bool(pred.left, env), subst_bool(pred.right, env))
    if isinstance(pred, SymNot):
        return SymNot(subst_bool(pred.operand, env))
    raise SiplSemanticError(f"Unknown SymBool node: {type(pred).__name__}")


def eval_sym_expr(expr: SymExpr, env: Mapping[str, int]) -> int:
    """Evaluate a ``SymExpr`` numerically under integer bindings ``env``."""
    if isinstance(expr, SymConst):
        return expr.value
    if isinstance(expr, SymVar):
        if expr.name not in env:
            raise SiplSemanticError(f"Undefined variable '{expr.name}' during evaluation")
        return env[expr.name]
    if isinstance(expr, SymAdd):
        return eval_sym_expr(expr.left, env) + eval_sym_expr(expr.right, env)
    if isinstance(expr, SymSub):
        return eval_sym_expr(expr.left, env) - eval_sym_expr(expr.right, env)
    if isinstance(expr, SymMul):
        return eval_sym_expr(expr.left, env) * eval_sym_expr(expr.right, env)
    if isinstance(expr, SymDiv):
        left = eval_sym_expr(expr.left, env)
        right = eval_sym_expr(expr.right, env)
        if right == 0:
            raise SiplSemanticError("Division by zero in symbolic expression")
        return left // right
    if isinstance(expr, SymMod):
        left = eval_sym_expr(expr.left, env)
        right = eval_sym_expr(expr.right, env)
        if right == 0:
            raise SiplSemanticError("Modulo by zero in symbolic expression")
        return left % right
    if isinstance(expr, SymPow):
        base = eval_sym_expr(expr.base, env)
        exp = eval_sym_expr(expr.exp, env)
        if exp < 0:
            raise SiplSemanticError(f"Negative exponent ({exp}) in integer symbolic evaluation")
        if exp > 2000 and abs(base) > 1:
            raise SiplSemanticError(f"Exponent too large ({exp}) for concrete evaluation")
        return int(base**exp)
    if isinstance(expr, SymFact):
        arg = eval_sym_expr(expr.arg, env)
        if arg < 0:
            raise SiplSemanticError(f"Factorial of negative integer ({arg})")
        if arg > 100:
            raise SiplSemanticError(f"Factorial argument too large ({arg})")
        return math.factorial(arg)
    if isinstance(expr, SymIf):
        if eval_sym_bool(expr.cond, env):
            return eval_sym_expr(expr.then_e, env)
        return eval_sym_expr(expr.else_e, env)
    raise SiplSemanticError(f"Unknown SymExpr node: {type(expr).__name__}")


def eval_sym_bool(pred: SymBool, env: Mapping[str, int]) -> bool:
    """Evaluate a ``SymBool`` predicate numerically under integer bindings ``env``."""
    if isinstance(pred, SymBoolConst):
        return pred.value
    if isinstance(pred, SymCmp):
        left = eval_sym_expr(pred.left, env)
        right = eval_sym_expr(pred.right, env)
        if pred.op in ("=", "=="):
            return left == right
        if pred.op == ">":
            return left > right
        if pred.op == ">=":
            return left >= right
        if pred.op == "<":
            return left < right
        if pred.op == "<=":
            return left <= right
        if pred.op == "!=":
            return left != right
        raise SiplSemanticError(f"Unsupported comparison operator {pred.op!r}")
    if isinstance(pred, SymAnd):
        return eval_sym_bool(pred.left, env) and eval_sym_bool(pred.right, env)
    if isinstance(pred, SymOr):
        return eval_sym_bool(pred.left, env) or eval_sym_bool(pred.right, env)
    if isinstance(pred, SymNot):
        return not eval_sym_bool(pred.operand, env)
    raise SiplSemanticError(f"Unknown SymBool node: {type(pred).__name__}")


_Factors = tuple[tuple[SymExpr, SymExpr], ...]
_SOP = dict[_Factors, int]


def _expr_sort_key(expr: SymExpr) -> tuple[int, str]:
    if isinstance(expr, SymConst):
        return (0, str(expr.value))
    if isinstance(expr, SymVar):
        return (1, expr.name)
    return (2, repr(expr))


def _sop_zero() -> _SOP:
    return {}


def _sop_const(val: int) -> _SOP:
    return {} if val == 0 else {(): val}


def _sop_atom(atom: SymExpr, exp: SymExpr | None = None) -> _SOP:
    if exp is None:
        exp = SymConst(1)
    if isinstance(exp, SymConst) and exp.value == 0:
        return {(): 1}
    if isinstance(atom, SymConst):
        if isinstance(exp, SymConst) and 0 <= exp.value <= 64:
            return _sop_const(int(atom.value**exp.value))
        if atom.value == 1:
            return {(): 1}
        if atom.value == 0 and isinstance(exp, SymConst) and exp.value > 0:
            return {}
    return {((atom, exp),): 1}


def _sop_add(a: _SOP, b: _SOP) -> _SOP:
    res = dict(a)
    for factors, coeff in b.items():
        new_c = res.get(factors, 0) + coeff
        if new_c == 0:
            res.pop(factors, None)
        else:
            res[factors] = new_c
    return res


def _sop_scale(a: _SOP, factor: int) -> _SOP:
    if factor == 0:
        return {}
    if factor == 1:
        return dict(a)
    return {factors: coeff * factor for factors, coeff in a.items()}


def _sop_sub(a: _SOP, b: _SOP) -> _SOP:
    return _sop_add(a, _sop_scale(b, -1))


def _normalize_factors(coeff: int, factor_map: dict[SymExpr, SymExpr]) -> tuple[int, _Factors]:
    """Combine constant multipliers with constant-base exponentials and sort factors."""
    if coeff == 0:
        return 0, ()
    cleaned: dict[SymExpr, SymExpr] = {}
    for base, exp in factor_map.items():
        s_exp = _simplify_raw(exp)
        if isinstance(s_exp, SymConst):
            if s_exp.value == 0:
                continue
            if isinstance(base, SymConst) and 0 <= s_exp.value <= 64:
                coeff *= int(base.value**s_exp.value)
                continue
        if isinstance(base, SymConst):
            if base.value == 1:
                continue
            if base.value == 0 and isinstance(s_exp, SymConst) and s_exp.value > 0:
                return 0, ()
            if base.value > 1:
                added = 0
                while coeff % base.value == 0:
                    coeff //= base.value
                    added += 1
                if added > 0:
                    s_exp = _simplify_raw(SymAdd(s_exp, SymConst(added)))
                    if isinstance(s_exp, SymConst) and 0 <= s_exp.value <= 64:
                        coeff *= int(base.value**s_exp.value)
                        continue
        cleaned[base] = s_exp
    ordered = tuple(sorted(cleaned.items(), key=lambda kv: _expr_sort_key(kv[0])))
    return coeff, ordered


def _mul_monomials(c1: int, f1: _Factors, c2: int, f2: _Factors) -> tuple[int, _Factors]:
    coeff = c1 * c2
    if coeff == 0:
        return 0, ()
    merged: dict[SymExpr, SymExpr] = dict(f1)
    for base, exp in f2:
        if base in merged:
            merged[base] = _simplify_raw(SymAdd(merged[base], exp))
        else:
            merged[base] = exp
    return _normalize_factors(coeff, merged)


def _sop_mul(a: _SOP, b: _SOP) -> _SOP:
    if not a or not b:
        return {}
    res: _SOP = {}
    for f1, c1 in a.items():
        for f2, c2 in b.items():
            coeff, factors = _mul_monomials(c1, f1, c2, f2)
            if coeff == 0:
                continue
            new_c = res.get(factors, 0) + coeff
            if new_c == 0:
                res.pop(factors, None)
            else:
                res[factors] = new_c
    return res


def _collapse_factorial_terms(sop: _SOP) -> _SOP:
    """Collapse ``(arg + 1) * arg!`` patterns inside a SOP sum into ``(arg + 1)!``."""
    changed = True
    current = dict(sop)
    while changed:
        changed = False
        fact_bases: list[SymExpr] = []
        seen: set[SymExpr] = set()
        for factors in current:
            for base, exp in factors:
                if isinstance(base, SymFact) and isinstance(exp, SymConst) and exp.value == 1:
                    if base not in seen:
                        seen.add(base)
                        fact_bases.append(base)
        for f_base in fact_bases:
            assert isinstance(f_base, SymFact)
            arg = f_base.arg
            target_sop = _expr_to_sop(SymAdd(arg, SymConst(1)))
            if not target_sop:
                continue
            sub: _SOP = {}
            rest_all: _SOP = {}
            for factors, coeff in current.items():
                if (f_base, SymConst(1)) in factors:
                    stripped = tuple(
                        (b, e) for b, e in factors if not (b == f_base and e == SymConst(1))
                    )
                    sub[stripped] = sub.get(stripped, 0) + coeff
                else:
                    rest_all[factors] = coeff
            if len(sub) == len(target_sop):
                ratios: set[int] = set()
                ok = True
                for tf, tc in target_sop.items():
                    if tf not in sub or sub[tf] % tc != 0:
                        ok = False
                        break
                    ratios.add(sub[tf] // tc)
                if ok and len(ratios) == 1:
                    scale = next(iter(ratios))
                    next_fact = SymFact(_simplify_raw(SymAdd(arg, SymConst(1))))
                    replacement = _sop_scale(_sop_atom(next_fact), scale)
                    current = _sop_add(rest_all, replacement)
                    changed = True
                    break
            if len(sub) >= len(target_sop) and len(target_sop) >= 2:
                common = set.intersection(*(set(f) for f in sub)) if sub else set()
                if common:
                    common_tuple = tuple(sorted(common, key=lambda kv: _expr_sort_key(kv[0])))
                    reduced_sub: _SOP = {}
                    for f, c in sub.items():
                        rem = tuple(kv for kv in f if kv not in common)
                        reduced_sub[rem] = reduced_sub.get(rem, 0) + c
                    if len(reduced_sub) == len(target_sop):
                        ratios = set()
                        ok = True
                        for tf, tc in target_sop.items():
                            if tf not in reduced_sub or reduced_sub[tf] % tc != 0:
                                ok = False
                                break
                            ratios.add(reduced_sub[tf] // tc)
                        if ok and len(ratios) == 1:
                            scale = next(iter(ratios))
                            next_fact = SymFact(_simplify_raw(SymAdd(arg, SymConst(1))))
                            merged_factors: dict[SymExpr, SymExpr] = dict(common_tuple)
                            merged_factors[next_fact] = SymConst(1)
                            new_factors = tuple(
                                sorted(
                                    merged_factors.items(),
                                    key=lambda kv: _expr_sort_key(kv[0]),
                                )
                            )
                            current = _sop_add(rest_all, {new_factors: scale})
                            changed = True
                            break
    return current


def _expr_to_sop(expr: SymExpr) -> _SOP:
    if isinstance(expr, SymConst):
        return _sop_const(expr.value)
    if isinstance(expr, SymVar):
        return _sop_atom(expr)
    if isinstance(expr, SymAdd):
        return _collapse_factorial_terms(
            _sop_add(_expr_to_sop(expr.left), _expr_to_sop(expr.right))
        )
    if isinstance(expr, SymSub):
        return _collapse_factorial_terms(
            _sop_sub(_expr_to_sop(expr.left), _expr_to_sop(expr.right))
        )
    if isinstance(expr, SymMul):
        return _collapse_factorial_terms(
            _sop_mul(_expr_to_sop(expr.left), _expr_to_sop(expr.right))
        )
    if isinstance(expr, SymPow):
        base = _simplify_raw(expr.base)
        exp = _simplify_raw(expr.exp)
        if isinstance(exp, SymConst):
            if exp.value == 0:
                return {(): 1}
            if exp.value == 1:
                return _expr_to_sop(base)
            if isinstance(base, SymConst) and 0 <= exp.value <= 64:
                return _sop_const(int(base.value**exp.value))
            if 2 <= exp.value <= 8:
                res = _sop_const(1)
                base_sop = _expr_to_sop(base)
                for _ in range(exp.value):
                    res = _sop_mul(res, base_sop)
                return _collapse_factorial_terms(res)
        if isinstance(base, SymConst) and base.value == 1:
            return {(): 1}
        if isinstance(base, SymPow):
            combined_exp = _simplify_raw(SymMul(base.exp, exp))
            return _expr_to_sop(SymPow(base.base, combined_exp))
        if isinstance(base, SymMul):
            return _expr_to_sop(SymMul(SymPow(base.left, exp), SymPow(base.right, exp)))
        if isinstance(base, SymConst) and base.value < 0:
            return _sop_atom(base, exp)
        if isinstance(base, (SymConst, SymVar, SymDiv, SymMod, SymFact, SymIf)):
            return _sop_atom(base, exp)
        return _sop_atom(SymPow(base, exp))
    if isinstance(expr, SymDiv):
        left = _simplify_raw(expr.left)
        right = _simplify_raw(expr.right)
        if isinstance(right, SymConst) and right.value == 1:
            return _expr_to_sop(left)
        if isinstance(left, SymConst) and isinstance(right, SymConst) and right.value != 0:
            return _sop_const(left.value // right.value)
        if sym_equals_structural(left, right) and isinstance(right, SymConst) and right.value != 0:
            return {(): 1}
        return _sop_atom(SymDiv(left, right))
    if isinstance(expr, SymMod):
        left = _simplify_raw(expr.left)
        right = _simplify_raw(expr.right)
        if isinstance(right, SymConst) and right.value == 1:
            return {}
        if isinstance(left, SymConst) and isinstance(right, SymConst) and right.value != 0:
            return _sop_const(left.value % right.value)
        return _sop_atom(SymMod(left, right))
    if isinstance(expr, SymFact):
        arg = _simplify_raw(expr.arg)
        if isinstance(arg, SymConst) and 0 <= arg.value <= 20:
            return _sop_const(math.factorial(arg.value))
        return _sop_atom(SymFact(arg))
    if isinstance(expr, SymIf):
        s_cond = simplify_bool(expr.cond)
        s_then = _simplify_raw(expr.then_e)
        s_else = _simplify_raw(expr.else_e)
        if isinstance(s_cond, SymBoolConst):
            return _expr_to_sop(s_then if s_cond.value else s_else)
        if sym_equals_structural(s_then, s_else):
            return _expr_to_sop(s_then)
        return _sop_atom(SymIf(s_cond, s_then, s_else))
    raise SiplSemanticError(f"Unknown SymExpr node: {type(expr).__name__}")


def _factors_to_expr(factors: _Factors) -> SymExpr:
    if not factors:
        return SymConst(1)
    parts: list[SymExpr] = []
    for base, exp in factors:
        if isinstance(exp, SymConst) and exp.value == 1:
            parts.append(base)
        else:
            parts.append(SymPow(base, exp))
    acc = parts[0]
    for p in parts[1:]:
        acc = SymMul(acc, p)
    return acc


def _monomial_to_expr(coeff: int, factors: _Factors) -> SymExpr:
    if not factors:
        return SymConst(coeff)
    body = _factors_to_expr(factors)
    if coeff == 1:
        return body
    if coeff == -1:
        return SymSub(SymConst(0), body)
    return SymMul(SymConst(coeff), body)


def _sop_term_sort_key(item: tuple[_Factors, int]) -> tuple[int, int, str]:
    factors, _coeff = item
    if not factors:
        return (2, 0, "")
    deg = sum(e.value if isinstance(e, SymConst) else 3 for _, e in factors)
    return (0 if deg >= 1 else 1, -deg, "|".join(_expr_sort_key(b)[1] for b, _ in factors))


def _group_and_build_sum(terms: list[tuple[_Factors, int]]) -> SymExpr:
    """Build a readable sum of positive-coefficient monomials, factoring shared trailing vars."""
    if not terms:
        return SymConst(0)
    if len(terms) >= 2:
        common = set.intersection(*(set(f) for f, _ in terms))
        if common:
            shared_pair = sorted(common, key=lambda kv: _expr_sort_key(kv[0]))[-1]
            rem_sop: _SOP = {}
            for f, c in terms:
                rem = tuple(kv for kv in f if kv != shared_pair)
                rem_sop[rem] = rem_sop.get(rem, 0) + c
            inner = _sop_to_expr(rem_sop)
            shared_expr = _factors_to_expr((shared_pair,))
            return (
                SymMul(inner, shared_expr)
                if isinstance(inner, (SymAdd, SymSub))
                else SymMul(inner, shared_expr)
            )
    acc = _monomial_to_expr(terms[0][1], terms[0][0])
    for factors, coeff in terms[1:]:
        acc = SymAdd(acc, _monomial_to_expr(coeff, factors))
    return acc


def _sop_to_expr(sop: _SOP) -> SymExpr:
    if not sop:
        return SymConst(0)
    pos_terms = sorted(
        [(f, c) for f, c in sop.items() if c > 0],
        key=_sop_term_sort_key,
    )
    neg_terms = sorted(
        [(f, -c) for f, c in sop.items() if c < 0],
        key=_sop_term_sort_key,
    )

    if not neg_terms:
        return _group_and_build_sum(pos_terms)
    if not pos_terms:
        neg_sum = _group_and_build_sum(neg_terms)
        if isinstance(neg_sum, SymConst):
            return SymConst(-neg_sum.value)
        return SymSub(SymConst(0), neg_sum)

    pos_expr = _group_and_build_sum(pos_terms)
    neg_expr = _group_and_build_sum(neg_terms)
    return SymSub(pos_expr, neg_expr)


def _simplify_raw(expr: SymExpr) -> SymExpr:
    return _sop_to_expr(_expr_to_sop(expr))


def simplify(expr: SymExpr) -> SymExpr:
    """Algebraically simplify and canonicalize ``expr``."""
    return _simplify_raw(expr)


def simplify_bool(pred: SymBool) -> SymBool:
    """Simplify a symbolic boolean predicate ``pred``."""
    if isinstance(pred, SymBoolConst):
        return pred
    if isinstance(pred, SymCmp):
        left = simplify(pred.left)
        right = simplify(pred.right)
        diff = simplify(SymSub(left, right))
        if isinstance(diff, SymConst):
            d = diff.value
            if pred.op in ("=", "=="):
                return SymBoolConst(d == 0)
            if pred.op == ">":
                return SymBoolConst(d > 0)
            if pred.op == ">=":
                return SymBoolConst(d >= 0)
            if pred.op == "<":
                return SymBoolConst(d < 0)
            if pred.op == "<=":
                return SymBoolConst(d <= 0)
            if pred.op == "!=":
                return SymBoolConst(d != 0)
        return SymCmp(pred.op, left, right)
    if isinstance(pred, SymAnd):
        b_left = simplify_bool(pred.left)
        b_right = simplify_bool(pred.right)
        if isinstance(b_left, SymBoolConst):
            return b_right if b_left.value else SymBoolConst(False)
        if isinstance(b_right, SymBoolConst):
            return b_left if b_right.value else SymBoolConst(False)
        if b_left == b_right:
            return b_left
        return SymAnd(b_left, b_right)
    if isinstance(pred, SymOr):
        o_left = simplify_bool(pred.left)
        o_right = simplify_bool(pred.right)
        if isinstance(o_left, SymBoolConst):
            return SymBoolConst(True) if o_left.value else o_right
        if isinstance(o_right, SymBoolConst):
            return SymBoolConst(True) if o_right.value else o_left
        if o_left == o_right:
            return o_left
        return SymOr(o_left, o_right)
    if isinstance(pred, SymNot):
        inner = simplify_bool(pred.operand)
        if isinstance(inner, SymBoolConst):
            return SymBoolConst(not inner.value)
        if isinstance(inner, SymNot):
            return inner.operand
        if isinstance(inner, SymCmp):
            neg_op = {
                "=": "!=",
                "!=": "=",
                ">": "<=",
                "<=": ">",
                ">=": "<",
                "<": ">=",
            }[inner.op]
            return SymCmp(neg_op, inner.left, inner.right)
        return SymNot(inner)
    raise SiplSemanticError(f"Unknown SymBool node: {type(pred).__name__}")


def _has_non_poly_ops(expr: SymExpr) -> bool:
    if isinstance(expr, (SymConst, SymVar)):
        return False
    if isinstance(expr, (SymDiv, SymMod, SymFact, SymIf)):
        return True
    if isinstance(expr, (SymAdd, SymSub, SymMul)):
        return _has_non_poly_ops(expr.left) or _has_non_poly_ops(expr.right)
    if isinstance(expr, SymPow):
        if not isinstance(expr.exp, SymConst) or expr.exp.value > 8:
            return True
        return _has_non_poly_ops(expr.base)
    return True


def sym_equals_structural(a: SymExpr, b: SymExpr) -> bool:
    """Check algebraic equality strictly via canonical SOP form."""
    return _expr_to_sop(a) == _expr_to_sop(b)


def sym_equals(a: SymExpr, b: SymExpr) -> bool:
    """Check whether ``a`` and ``b`` are algebraically equivalent.

    Uses canonical sum-of-products (SOP) normalization first; when expressions
    involve ``div``, ``mod``, ``!``, ``if``, or symbolic powers that did not
    structurally collapse, falls back to multi-point integer evaluation.
    """
    sop_a = _expr_to_sop(a)
    sop_b = _expr_to_sop(b)
    if sop_a == sop_b:
        return True
    if not _sop_sub(sop_a, sop_b):
        return True

    sa = _sop_to_expr(sop_a)
    sb = _sop_to_expr(sop_b)
    if not _has_non_poly_ops(sa) and not _has_non_poly_ops(sb):
        return False

    vars_list = sorted(sa.free_vars() | sb.free_vars())
    if not vars_list:
        try:
            return eval_sym_expr(sa, {}) == eval_sym_expr(sb, {})
        except SiplSemanticError:
            return False

    sample_values = [1, 2, 3, 4, 5, 7, 10]
    tested = 0
    for trial in range(16):
        env: dict[str, int] = {}
        for idx, var in enumerate(vars_list):
            env[var] = sample_values[(trial * 3 + idx * 2 + 1) % len(sample_values)] + (
                trial // len(sample_values)
            )
        try:
            va = eval_sym_expr(sa, env)
            vb = eval_sym_expr(sb, env)
        except SiplSemanticError:
            continue
        tested += 1
        if va != vb:
            return False
    return tested >= 5
