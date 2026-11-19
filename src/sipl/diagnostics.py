"""Source locations, structured diagnostics, and SIPL exception hierarchy."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True, slots=True)
class SourcePosition:
    """A 1-based line/column and 0-based character offset in source text."""

    line: int
    column: int
    offset: int

    def to_dict(self) -> dict[str, int]:
        """Return a JSON-serializable representation of this position."""
        return {
            "line": self.line,
            "column": self.column,
            "offset": self.offset,
        }


@dataclass(frozen=True, slots=True)
class SourceSpan:
    """A half-open source range ``[start, end)`` between two positions."""

    start: SourcePosition
    end: SourcePosition

    def merge(self, other: SourceSpan) -> SourceSpan:
        """Return the smallest span covering both ``self`` and ``other``."""
        start = self.start if self.start.offset <= other.start.offset else other.start
        end = self.end if self.end.offset >= other.end.offset else other.end
        return SourceSpan(start=start, end=end)

    def to_dict(self) -> dict[str, Any]:
        """Return a JSON-serializable representation of this span."""
        return {
            "start": self.start.to_dict(),
            "end": self.end.to_dict(),
        }


@dataclass(frozen=True, slots=True)
class Diagnostic:
    """Structured compiler/interpreter diagnostic bound to a ``SourceSpan``."""

    code: str
    message: str
    span: SourceSpan
    severity: str = "error"
    hint: str | None = None

    def to_dict(self) -> dict[str, Any]:
        """Return a JSON-serializable representation of this diagnostic."""
        data: dict[str, Any] = {
            "code": self.code,
            "severity": self.severity,
            "message": self.message,
            "span": self.span.to_dict(),
        }
        if self.hint is not None:
            data["hint"] = self.hint
        return data

    def format_with_source(self, source: str) -> str:
        """Render a human-readable snippet with line numbers and ``^~~~`` underline."""
        lines = source.splitlines()
        line_no = max(1, self.span.start.line)
        col_no = max(1, self.span.start.column)
        gutter_width = len(str(line_no))

        header = f"{self.severity}[{self.code}]: {self.message}"
        loc = f"{' ' * gutter_width} --> line {line_no}, column {col_no}"

        if not lines or line_no > len(lines):
            source_line = ""
            underline_len = 1
        else:
            source_line = lines[line_no - 1]
            if self.span.end.line == self.span.start.line:
                underline_len = max(1, self.span.end.column - self.span.start.column)
            else:
                underline_len = max(1, len(source_line) - col_no + 1)

        caret = "^" + ("~" * max(0, underline_len - 1))
        pad = " " * max(0, col_no - 1)
        blank_gutter = " " * gutter_width
        parts = [
            header,
            loc,
            f"{blank_gutter} |",
            f"{line_no:>{gutter_width}} | {source_line}",
            f"{blank_gutter} | {pad}{caret}",
        ]
        if self.hint:
            parts.append(f"{blank_gutter} = hint: {self.hint}")
        return "\n".join(parts)


class SiplError(Exception):
    """Base exception for all SIPL toolkit errors."""

    def __init__(self, message: str, diagnostic: Diagnostic | None = None) -> None:
        super().__init__(message)
        self.diagnostic = diagnostic


class SiplSyntaxError(SiplError):
    """Raised when lexing or parsing SIPL source fails."""

    def __init__(self, diagnostic: Diagnostic) -> None:
        self.diagnostic: Diagnostic = diagnostic
        loc = f"line {diagnostic.span.start.line}, column {diagnostic.span.start.column}"
        super().__init__(f"[{diagnostic.code}] {diagnostic.message} ({loc})", diagnostic=diagnostic)


class SiplSemanticError(SiplError):
    """Raised for semantic-layer errors (term construction, proof checking, etc.)."""


class SiplRuntimeError(SiplError):
    """Raised on runtime evaluation errors (undefined variable, division by zero, step limit)."""

    def __init__(
        self,
        message: str,
        *,
        code: str = "E_RUNTIME",
        span: SourceSpan | None = None,
        diagnostic: Diagnostic | None = None,
    ) -> None:
        self.code = code
        self.span = span
        if diagnostic is None and span is not None:
            diagnostic = Diagnostic(code=code, message=message, span=span, severity="error")
        super().__init__(message, diagnostic=diagnostic)


SipError = SiplError
SipSyntaxError = SiplSyntaxError
SipSemanticError = SiplSemanticError
SipRuntimeError = SiplRuntimeError
