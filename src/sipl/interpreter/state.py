"""Immutable variable state algebra (``State = Var -> Int``, overlay ∇, extension ⊆)."""

from __future__ import annotations

import re
from collections.abc import Iterator, Mapping

from sipl.diagnostics import SiplRuntimeError

_ENTRY_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:\u21a6|->|=)\s*([-\u2013\u2212]?\d+)\s*$"
)


class StateParseError(SiplRuntimeError, ValueError):
    """Raised when a textual SIPL state specification cannot be parsed."""


class State:
    """Immutable / copy-on-write mapping from SIPL variable names to integers.

    Implements the course state algebra ``A_State = <State; ∇>``:
    - ``st1.overlay(st2)`` computes ``st1 ∇ st2`` (entries in ``st2`` override ``st1``).
    - ``st1.is_substate_of(st2)`` checks ``st1 ⊆ st2``.
    - ``format_course()`` formats as ``[X ↦ 5, Y ↦ 2]``.
    """

    __slots__ = ("_data",)

    def __init__(self, mapping: Mapping[str, int] | None = None) -> None:
        if mapping is None:
            self._data: dict[str, int] = {}
        else:
            cleaned: dict[str, int] = {}
            for k, v in mapping.items():
                if not isinstance(k, str) or not k:
                    raise ValueError(f"Variable name must be a non-empty string, got {k!r}")
                if isinstance(v, bool) or not isinstance(v, int):
                    raise ValueError(f"State value for '{k}' must be int, got {v!r}")
                cleaned[k] = v
            self._data = cleaned

    @classmethod
    def parse(cls, text: str) -> State:
        """Parse a state string such as ``'X=5, Y=2'`` or ``'[X ↦ 5, Y ↦ 2]'``."""
        stripped = text.strip()
        if not stripped:
            return cls()

        if stripped.startswith("[") and stripped.endswith("]"):
            stripped = stripped[1:-1].strip()
        elif stripped.startswith("[") or stripped.endswith("]"):
            raise StateParseError(f"Unmatched bracket in state specification: {text!r}")

        if not stripped:
            return cls()

        parts = [part for part in re.split(r"[,;]", stripped) if part.strip()]
        mapping: dict[str, int] = {}
        for part in parts:
            match = _ENTRY_RE.match(part)
            if match is None:
                raise StateParseError(
                    f"Invalid state binding {part.strip()!r}; "
                    "expected 'Var = Int', 'Var ↦ Int', or 'Var -> Int'"
                )
            var, raw_val = match.groups()
            val = int(raw_val.replace("\u2013", "-").replace("\u2212", "-"))
            mapping[var] = val
        return cls(mapping)

    def get(self, var: str, default: int | None = None) -> int | None:
        """Return the integer bound to ``var``, or ``default`` (``None``) if unbound."""
        return self._data.get(var, default)

    def __getitem__(self, var: str) -> int:
        if var not in self._data:
            raise SiplRuntimeError(f"Undefined variable '{var}'", code="E_UNDEFINED_VAR")
        return self._data[var]

    def __contains__(self, var: object) -> bool:
        return var in self._data

    def __len__(self) -> int:
        return len(self._data)

    def __iter__(self) -> Iterator[str]:
        return iter(self._data)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, State):
            return self._data == other._data
        return NotImplemented

    def keys(self) -> list[str]:
        return list(self._data.keys())

    def values(self) -> list[int]:
        return list(self._data.values())

    def items(self) -> list[tuple[str, int]]:
        return list(self._data.items())

    def overlay(self, other: State | Mapping[str, int]) -> State:
        """Return ``self ∇ other`` where bindings in ``other`` override those in ``self``."""
        merged = dict(self._data)
        if isinstance(other, State):
            merged.update(other._data)
        else:
            for k, v in other.items():
                if isinstance(v, bool) or not isinstance(v, int):
                    raise ValueError(f"State value for '{k}' must be int, got {v!r}")
                merged[k] = v
        return State(merged)

    def with_var(self, var: str, value: int) -> State:
        """Return a new ``State`` equal to ``self ∇ [var ↦ value]``."""
        return self.overlay({var: value})

    def is_substate_of(self, other: State) -> bool:
        """Return ``True`` iff ``self ⊆ other`` (every binding in ``self`` matches ``other``)."""
        return all(other.get(k) == v for k, v in self._data.items())

    def format_course(self) -> str:
        """Format state in course notation, e.g. ``[X ↦ 5, Y ↦ 2]``."""
        inner = ", ".join(f"{k} \u21a6 {v}" for k, v in self._data.items())
        return f"[{inner}]"

    def to_dict(self) -> dict[str, int]:
        """Return a mutable copy of the state mapping for JSON serialization."""
        return dict(self._data)

    def __str__(self) -> str:
        return self.format_course()

    def __repr__(self) -> str:
        return f"State({self._data!r})"
