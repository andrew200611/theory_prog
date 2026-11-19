"""Lexical analyzer (tokenizer) for SIPL."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from sipl.diagnostics import Diagnostic, SiplSyntaxError, SourcePosition, SourceSpan

_CORE_KEYWORDS: dict[str, str] = {
    "begin": "KW_BEGIN",
    "end": "KW_END",
    "if": "KW_IF",
    "then": "KW_THEN",
    "else": "KW_ELSE",
    "while": "KW_WHILE",
    "do": "KW_DO",
    "skip": "KW_SKIP",
}

_EXTENDED_KEYWORDS: dict[str, str] = {
    "div": "DIV",
    "mod": "MOD",
    "or": "OR",
    "not": "NOT",
    "and": "AND",
}

_MINUS_CHARS = frozenset({"-", "\u2013", "\u2212"})
_VALUE_ENDING_KINDS = frozenset({"IDENT", "NUM", "RPAREN"})


@dataclass(frozen=True, slots=True)
class Token:
    """A single lexical token with its kind, exact source text, and ``SourceSpan``."""

    kind: str
    value: str
    span: SourceSpan

    def to_dict(self) -> dict[str, Any]:
        """Return a JSON-serializable representation of this token."""
        return {
            "kind": self.kind,
            "value": self.value,
            "span": self.span.to_dict(),
        }


class _Lexer:
    """Internal stateful scanner tracking 1-based line/column and 0-based offset."""

    def __init__(self, source: str, *, strict_bnf: bool = False) -> None:
        self.source = source
        self.length = len(source)
        self.strict_bnf = strict_bnf
        self.offset = 0
        self.line = 1
        self.column = 1

    def _pos(self) -> SourcePosition:
        return SourcePosition(line=self.line, column=self.column, offset=self.offset)

    def _peek(self, ahead: int = 0) -> str:
        idx = self.offset + ahead
        if idx >= self.length:
            return ""
        return self.source[idx]

    def _advance(self, count: int = 1) -> str:
        chunk = self.source[self.offset : self.offset + count]
        for ch in chunk:
            if ch == "\n":
                self.line += 1
                self.column = 1
            else:
                self.column += 1
            self.offset += 1
        return chunk

    def _error(
        self,
        code: str,
        message: str,
        start: SourcePosition,
        end: SourcePosition | None = None,
        hint: str | None = None,
    ) -> SiplSyntaxError:
        span = SourceSpan(start=start, end=end or self._pos())
        return SiplSyntaxError(Diagnostic(code=code, message=message, span=span, hint=hint))

    def _skip_whitespace_and_comments(self) -> None:
        while self.offset < self.length:
            ch = self._peek()
            if ch in (" ", "\t", "\r", "\n"):
                self._advance()
                continue
            if ch == "#" or (ch == "/" and self._peek(1) == "/"):
                while self.offset < self.length and self._peek() != "\n":
                    self._advance()
                continue
            if ch == "(" and self._peek(1) == "*":
                start = self._pos()
                self._advance(2)
                closed = False
                while self.offset < self.length:
                    if self._peek() == "*" and self._peek(1) == ")":
                        self._advance(2)
                        closed = True
                        break
                    self._advance()
                if not closed:
                    raise self._error(
                        "E_LEX_UNCLOSED_COMMENT",
                        "Unclosed block comment '(* ... *)'",
                        start,
                        SourcePosition(start.line, start.column + 2, start.offset + 2),
                        hint="Add closing '*)' before the end of the file",
                    )
                continue
            break

    def tokenize(self) -> list[Token]:
        tokens: list[Token] = []
        while True:
            self._skip_whitespace_and_comments()
            if self.offset >= self.length:
                break

            start = self._pos()
            ch = self._peek()
            nxt = self._peek(1)
            prev_kind = tokens[-1].kind if tokens else None

            if ch in _MINUS_CHARS and nxt.isdigit() and prev_kind not in _VALUE_ENDING_KINDS:
                self._advance()
                while self.offset < self.length and self._peek().isdigit():
                    self._advance()
                if self.offset < self.length and (self._peek().isalpha() or self._peek() == "_"):
                    bad = self.source[start.offset : self.offset + 1]
                    raise self._error(
                        "E_LEX_INVALID_NUMBER",
                        f"Invalid numeric literal '{bad}'",
                        start,
                        SourcePosition(self.line, self.column + 1, self.offset + 1),
                        hint="Separate numeric literals from identifiers",
                    )
                value = self.source[start.offset : self.offset]
                tokens.append(Token("NUM", value, SourceSpan(start, self._pos())))
                continue

            two = ch + nxt
            if two == ":=":
                self._advance(2)
                tokens.append(Token("ASSIGN", two, SourceSpan(start, self._pos())))
                continue
            if two == ">=":
                self._advance(2)
                tokens.append(Token("GE", two, SourceSpan(start, self._pos())))
                continue
            if two == "<=":
                self._advance(2)
                tokens.append(Token("LE", two, SourceSpan(start, self._pos())))
                continue
            if two in ("!=", "<>"):
                self._advance(2)
                tokens.append(Token("NE", two, SourceSpan(start, self._pos())))
                continue
            if two == "||":
                self._advance(2)
                tokens.append(Token("OR", two, SourceSpan(start, self._pos())))
                continue
            if two == "&&":
                self._advance(2)
                tokens.append(Token("AND", two, SourceSpan(start, self._pos())))
                continue

            if ch == ";":
                self._advance()
                tokens.append(Token("SEMICOLON", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "+":
                self._advance()
                tokens.append(Token("PLUS", ch, SourceSpan(start, self._pos())))
                continue
            if ch in _MINUS_CHARS:
                self._advance()
                tokens.append(Token("MINUS", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "*":
                self._advance()
                tokens.append(Token("MUL", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "=":
                self._advance()
                tokens.append(Token("EQ", ch, SourceSpan(start, self._pos())))
                continue
            if ch == ">":
                self._advance()
                tokens.append(Token("GT", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "<":
                self._advance()
                tokens.append(Token("LT", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "\u2265":
                self._advance()
                tokens.append(Token("GE", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "\u2264":
                self._advance()
                tokens.append(Token("LE", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "\u2260":
                self._advance()
                tokens.append(Token("NE", ch, SourceSpan(start, self._pos())))
                continue
            if ch in ("\u2228", "\uf0da"):
                self._advance()
                tokens.append(Token("OR", ch, SourceSpan(start, self._pos())))
                continue
            if ch in ("\u00ac", "\uf0d8", "!", "~"):
                self._advance()
                tokens.append(Token("NOT", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "\u2227":
                self._advance()
                tokens.append(Token("AND", ch, SourceSpan(start, self._pos())))
                continue
            if ch == "(":
                self._advance()
                tokens.append(Token("LPAREN", ch, SourceSpan(start, self._pos())))
                continue
            if ch == ")":
                self._advance()
                tokens.append(Token("RPAREN", ch, SourceSpan(start, self._pos())))
                continue

            if ch.isdigit():
                while self.offset < self.length and self._peek().isdigit():
                    self._advance()
                if self.offset < self.length and (self._peek().isalpha() or self._peek() == "_"):
                    bad = self.source[start.offset : self.offset + 1]
                    raise self._error(
                        "E_LEX_INVALID_NUMBER",
                        f"Invalid numeric literal '{bad}'",
                        start,
                        SourcePosition(self.line, self.column + 1, self.offset + 1),
                        hint="Variable names cannot start with a digit",
                    )
                value = self.source[start.offset : self.offset]
                tokens.append(Token("NUM", value, SourceSpan(start, self._pos())))
                continue

            if ch.isalpha() or ch == "_":
                while self.offset < self.length and (
                    self._peek().isalnum() or self._peek() == "_"
                ):
                    self._advance()
                value = self.source[start.offset : self.offset]
                kind = _CORE_KEYWORDS.get(value)
                if kind is None and not self.strict_bnf:
                    kind = _EXTENDED_KEYWORDS.get(value)
                if kind is None:
                    kind = "IDENT"
                tokens.append(Token(kind, value, SourceSpan(start, self._pos())))
                continue

            if ch == ":":
                self._advance()
                raise self._error(
                    "E_LEX_STRAY_COLON",
                    "Unexpected ':' (expected ':=')",
                    start,
                    hint="Use ':=' for assignment in SIPL",
                )
            if ch == "|":
                self._advance()
                raise self._error(
                    "E_LEX_STRAY_PIPE",
                    "Unexpected '|' (expected '||' or '∨' / 'or')",
                    start,
                    hint="Use '∨', 'or', or '||' for disjunction",
                )
            if ch == "&":
                self._advance()
                raise self._error(
                    "E_LEX_STRAY_AMP",
                    "Unexpected '&' (expected '&&' or '∧' / 'and')",
                    start,
                    hint="Use '∧', 'and', or '&&' for conjunction",
                )

            self._advance()
            raise self._error(
                "E_LEX_UNKNOWN_CHAR",
                f"Unexpected character {ch!r}",
                start,
            )

        return tokens


def tokenize(source: str, *, strict_bnf: bool = False) -> list[Token]:
    """Lex SIPL ``source`` into a list of non-whitespace/non-comment ``Token`` objects.

    Raises ``SiplSyntaxError`` with an exact ``SourceSpan`` on invalid characters
    or malformed tokens.
    """
    return _Lexer(source, strict_bnf=strict_bnf).tokenize()
