"""Recursive-descent parser for SIPL producing both typed AST and concrete Parse Tree."""

from __future__ import annotations

from dataclasses import dataclass
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
    ParseTreeNode,
    Program,
    Seq,
    Skip,
    Stm,
    Variable,
    While,
)
from sipl.diagnostics import Diagnostic, SiplSyntaxError, SourcePosition, SourceSpan
from sipl.lexer import Token, tokenize

_CANONICAL_AEXP_OP: dict[str, tuple[str, str]] = {
    "PLUS": ("+", "NA3"),
    "MINUS": ("-", "NA4"),
    "MUL": ("*", "NA5"),
    "DIV": ("div", "NA_DIV"),
    "MOD": ("mod", "NA_MOD"),
}

_CANONICAL_CMP_OP: dict[str, tuple[str, str]] = {
    "EQ": ("=", "NB1"),
    "GT": (">", "NB2"),
    "GE": (">=", "NB_GE"),
    "LT": ("<", "NB_LT"),
    "LE": ("<=", "NB_LE"),
    "NE": ("!=", "NB_NE"),
}

_EXTENDED_ONLY_KINDS = frozenset({"DIV", "MOD", "GE", "LT", "LE", "NE", "AND"})
_BEXP_DISAMBIG_KINDS = frozenset(
    {"EQ", "GT", "GE", "LT", "LE", "NE", "OR", "AND", "NOT"}
)


@dataclass(slots=True)
class ParseResult:
    """Combined result of parsing a SIPL source program."""

    ast: Program
    parse_tree: ParseTreeNode
    tokens: list[Token]
    crown_text: str
    is_crown_valid: bool
    source: str

    def to_dict(self) -> dict[str, Any]:
        """Serialize parse result into a JSON-compatible dictionary."""
        return {
            "ast": self.ast.to_dict(),
            "parse_tree": self.parse_tree.to_dict(),
            "tokens": [t.to_dict() for t in self.tokens],
            "crown_text": self.crown_text,
            "is_crown_valid": self.is_crown_valid,
            "numbered_crown": self.parse_tree.numbered_crown(),
        }


class _Parser:
    """Recursive-descent parser honoring exact SIPL operator precedence."""

    def __init__(self, tokens: list[Token], source: str, *, strict_bnf: bool = False) -> None:
        self.tokens = tokens
        self.source = source
        self.strict_bnf = strict_bnf
        self.pos = 0
        self._ast_counter = 0
        self._pt_counter = 0
        self._eof_span = self._compute_eof_span(source)

    @staticmethod
    def _compute_eof_span(source: str) -> SourceSpan:
        lines = source.split("\n")
        line = len(lines)
        col = len(lines[-1]) + 1
        offset = len(source)
        pos = SourcePosition(line=line, column=col, offset=offset)
        return SourceSpan(start=pos, end=pos)

    def _next_ast_id(self) -> str:
        self._ast_counter += 1
        return f"ast_{self._ast_counter}"

    def _next_pt_id(self) -> str:
        self._pt_counter += 1
        return f"pt_{self._pt_counter}"

    def _current(self, offset: int = 0) -> Token | None:
        idx = self.pos + offset
        if idx >= len(self.tokens):
            return None
        return self.tokens[idx]

    def _peek_kind(self, offset: int = 0) -> str | None:
        tok = self._current(offset)
        return tok.kind if tok is not None else None

    def _current_span(self) -> SourceSpan:
        tok = self._current()
        return tok.span if tok is not None else self._eof_span

    def _error(
        self,
        code: str,
        message: str,
        span: SourceSpan | None = None,
        hint: str | None = None,
    ) -> SiplSyntaxError:
        return SiplSyntaxError(
            Diagnostic(
                code=code,
                message=message,
                span=span or self._current_span(),
                hint=hint,
            )
        )

    def _check_strict_token(self, tok: Token) -> None:
        if not self.strict_bnf:
            return
        if tok.kind in _EXTENDED_ONLY_KINDS or tok.value in ("||", "!", "~", "&&", "\u2227"):
            raise self._error(
                "E_STRICT_BNF",
                f"Extended operator '{tok.value}' is not part of strict course BNF",
                tok.span,
                hint="Parse with strict_bnf=False to allow workbook extensions",
            )

    def _advance(self) -> Token:
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def _expect(
        self,
        kind: str,
        code: str,
        expected_desc: str,
        hint: str | None = None,
    ) -> Token:
        tok = self._current()
        if tok is None:
            raise self._error(
                code,
                f"Expected {expected_desc}, but reached end of input",
                self._eof_span,
                hint=hint,
            )
        if tok.kind != kind:
            raise self._error(
                code,
                f"Expected {expected_desc}, found '{tok.value}'",
                tok.span,
                hint=hint,
            )
        return self._advance()

    def _leaf(self, tok: Token, ast_node_id: str | None = None) -> ParseTreeNode:
        return ParseTreeNode(
            label=tok.value,
            category=None,
            rule_name=None,
            span=tok.span,
            node_id=self._next_pt_id(),
            children=[],
            is_terminal=True,
            token_text=tok.value,
            leaf_index=None,
            ast_node_id=ast_node_id,
        )

    def _pt(
        self,
        label: str,
        category: str,
        rule_name: str,
        children: list[ParseTreeNode],
        span: SourceSpan,
        ast_node_id: str,
    ) -> ParseTreeNode:
        return ParseTreeNode(
            label=label,
            category=category,
            rule_name=rule_name,
            span=span,
            node_id=self._next_pt_id(),
            children=children,
            is_terminal=False,
            token_text=None,
            leaf_index=None,
            ast_node_id=ast_node_id,
        )


    def parse(self) -> tuple[Program, ParseTreeNode]:
        if not self.tokens:
            raise self._error(
                "E_SYNTAX_EMPTY",
                "Empty SIPL program; expected 'begin <statement> end'",
                self._eof_span,
                hint="A SIPL program has the form: begin <statement> end",
            )

        begin_tok = self._current()
        if begin_tok is None or begin_tok.kind != "KW_BEGIN":
            found = begin_tok.value if begin_tok else "EOF"
            raise self._error(
                "E_SYNTAX_EXPECTED_BEGIN",
                f"SIPL program must start with 'begin', found '{found}'",
                begin_tok.span if begin_tok else self._eof_span,
                hint="Wrap your program in 'begin ... end'",
            )
        self._advance()

        if self._peek_kind() == "KW_END":
            end_tok = self._current()
            raise self._error(
                "E_SYNTAX_EMPTY_BLOCK",
                "Empty 'begin ... end' block is not allowed by SIPL BNF",
                end_tok.span if end_tok else self._eof_span,
                hint="Use 'skip' inside 'begin ... end' for a no-op program",
            )

        body_ast, body_pt = self._parse_seq_stm()

        end_tok = self._expect(
            "KW_END",
            "E_SYNTAX_EXPECTED_END",
            "'end' to close program",
            hint="Add matching 'end' at the end of the program",
        )

        if self._current() is not None:
            extra = self._current()
            assert extra is not None
            raise self._error(
                "E_SYNTAX_TRAILING_TOKENS",
                f"Unexpected token '{extra.value}' after program 'end'",
                extra.span,
                hint="Remove tokens after 'end' or wrap statements inside 'begin ... end'",
            )

        span = begin_tok.span.merge(end_tok.span)
        prog_ast = Program(body=body_ast, span=span, node_id=self._next_ast_id())
        prog_pt = self._pt(
            "<програма>",
            "Prog",
            "NP1",
            [self._leaf(begin_tok), body_pt, self._leaf(end_tok)],
            span,
            prog_ast.node_id,
        )
        self._assign_leaf_indices(prog_pt)
        return prog_ast, prog_pt

    def _assign_leaf_indices(self, root: ParseTreeNode) -> None:
        for idx, leaf in enumerate(root.leaves(), start=1):
            leaf.leaf_index = idx

    def _parse_seq_stm(self) -> tuple[Stm, ParseTreeNode]:
        left_ast, left_pt = self._parse_atomic_stm()
        while self._peek_kind() == "SEMICOLON":
            semi_tok = self._advance()
            nxt = self._current()
            if nxt is None or nxt.kind == "KW_END":
                raise self._error(
                    "E_SYNTAX_TRAILING_SEMICOLON",
                    "Unexpected ';' with no following statement",
                    semi_tok.span,
                    hint="Remove the trailing ';' before 'end'",
                )
            right_ast, right_pt = self._parse_atomic_stm()
            span = left_ast.span.merge(right_ast.span)
            seq_ast = Seq(left=left_ast, right=right_ast, span=span, node_id=self._next_ast_id())
            seq_pt = self._pt(
                "<оператор>",
                "Stm",
                "NS2",
                [left_pt, self._leaf(semi_tok), right_pt],
                span,
                seq_ast.node_id,
            )
            left_ast, left_pt = seq_ast, seq_pt
        return left_ast, left_pt

    def _parse_atomic_stm(self) -> tuple[Stm, ParseTreeNode]:
        tok = self._current()
        if tok is None:
            raise self._error(
                "E_SYNTAX_EXPECTED_STM",
                "Expected a statement, reached end of input",
                self._eof_span,
            )

        if tok.kind == "IDENT":
            return self._parse_assign_stm()
        if tok.kind == "KW_IF":
            return self._parse_if_stm()
        if tok.kind == "KW_WHILE":
            return self._parse_while_stm()
        if tok.kind == "KW_BEGIN":
            return self._parse_block_stm()
        if tok.kind == "KW_SKIP":
            return self._parse_skip_stm()

        if tok.kind in ("KW_ELSE", "KW_THEN", "KW_DO", "KW_END", "SEMICOLON"):
            raise self._error(
                "E_SYNTAX_UNEXPECTED_TOKEN",
                f"Expected a statement, found '{tok.value}'",
                tok.span,
            )

        raise self._error(
            "E_SYNTAX_EXPECTED_STM",
            f"Expected a statement (assign, 'if', 'while', 'begin', 'skip'), found '{tok.value}'",
            tok.span,
        )

    def _parse_assign_stm(self) -> tuple[Assign, ParseTreeNode]:
        var_tok = self._advance()
        nxt = self._current()
        if nxt is not None and nxt.kind == "EQ":
            raise self._error(
                "E_SYNTAX_EXPECTED_ASSIGN",
                "Expected ':=' in assignment, found '='",
                nxt.span,
                hint="Use ':=' for assignment in SIPL ('=' is only for comparisons)",
            )
        assign_tok = self._expect(
            "ASSIGN",
            "E_SYNTAX_EXPECTED_ASSIGN",
            "':=' after variable name",
            hint=f"Write '{var_tok.value} := <expression>'",
        )
        expr_ast, expr_pt = self._parse_aexp()
        span = var_tok.span.merge(expr_ast.span)
        ast_node = Assign(
            var=var_tok.value,
            expr=expr_ast,
            span=span,
            node_id=self._next_ast_id(),
            var_span=var_tok.span,
        )
        var_pt = self._pt(
            "<змінна>",
            "Var",
            "NV",
            [self._leaf(var_tok, ast_node.node_id)],
            var_tok.span,
            ast_node.node_id,
        )
        pt_node = self._pt(
            "<оператор>",
            "Stm",
            "NS1",
            [var_pt, self._leaf(assign_tok), expr_pt],
            span,
            ast_node.node_id,
        )
        return ast_node, pt_node

    def _parse_if_stm(self) -> tuple[If, ParseTreeNode]:
        if_tok = self._advance()
        cond_ast, cond_pt = self._parse_bexp()
        then_tok = self._expect(
            "KW_THEN",
            "E_SYNTAX_EXPECTED_THEN",
            "'then' after 'if' condition",
        )
        then_ast, then_pt = self._parse_atomic_stm()

        cur = self._current()
        if cur is not None and cur.kind == "SEMICOLON":
            raise self._error(
                "E_SYNTAX_EXPECTED_ELSE",
                "Expected 'else' after 'then' branch, found ';'",
                cur.span,
                hint=(
                    "In SIPL, ';' has lower precedence than 'if ... then ... else'. "
                    "Wrap multiple statements in 'begin ... end'."
                ),
            )

        else_tok = self._expect(
            "KW_ELSE",
            "E_SYNTAX_EXPECTED_ELSE",
            "'else' branch in 'if' statement",
            hint="In SIPL, 'if ... then ... else ...' requires 'else' (use 'else skip' if empty)",
        )
        else_ast, else_pt = self._parse_atomic_stm()
        span = if_tok.span.merge(else_ast.span)
        ast_node = If(
            cond=cond_ast,
            then_branch=then_ast,
            else_branch=else_ast,
            span=span,
            node_id=self._next_ast_id(),
        )
        pt_node = self._pt(
            "<оператор>",
            "Stm",
            "NS3",
            [
                self._leaf(if_tok),
                cond_pt,
                self._leaf(then_tok),
                then_pt,
                self._leaf(else_tok),
                else_pt,
            ],
            span,
            ast_node.node_id,
        )
        return ast_node, pt_node

    def _parse_while_stm(self) -> tuple[While, ParseTreeNode]:
        while_tok = self._advance()
        cond_ast, cond_pt = self._parse_bexp()
        do_tok = self._expect(
            "KW_DO",
            "E_SYNTAX_EXPECTED_DO",
            "'do' after 'while' condition",
        )
        body_ast, body_pt = self._parse_atomic_stm()
        span = while_tok.span.merge(body_ast.span)
        ast_node = While(
            cond=cond_ast,
            body=body_ast,
            span=span,
            node_id=self._next_ast_id(),
        )
        pt_node = self._pt(
            "<оператор>",
            "Stm",
            "NS4",
            [self._leaf(while_tok), cond_pt, self._leaf(do_tok), body_pt],
            span,
            ast_node.node_id,
        )
        return ast_node, pt_node

    def _parse_block_stm(self) -> tuple[Block, ParseTreeNode]:
        begin_tok = self._advance()
        if self._peek_kind() == "KW_END":
            end_tok = self._current()
            raise self._error(
                "E_SYNTAX_EMPTY_BLOCK",
                "Empty 'begin ... end' block is not allowed by SIPL BNF",
                end_tok.span if end_tok else self._eof_span,
                hint="Use 'skip' inside 'begin ... end' for an empty block",
            )
        body_ast, body_pt = self._parse_seq_stm()
        end_tok = self._expect(
            "KW_END",
            "E_SYNTAX_EXPECTED_END",
            "'end' to close 'begin' block",
            hint="Add matching 'end' for 'begin'",
        )
        span = begin_tok.span.merge(end_tok.span)
        ast_node = Block(body=body_ast, span=span, node_id=self._next_ast_id())
        pt_node = self._pt(
            "<оператор>",
            "Stm",
            "NS5",
            [self._leaf(begin_tok), body_pt, self._leaf(end_tok)],
            span,
            ast_node.node_id,
        )
        return ast_node, pt_node

    def _parse_skip_stm(self) -> tuple[Skip, ParseTreeNode]:
        skip_tok = self._advance()
        ast_node = Skip(span=skip_tok.span, node_id=self._next_ast_id())
        pt_node = self._pt(
            "<оператор>",
            "Stm",
            "NS6",
            [self._leaf(skip_tok, ast_node.node_id)],
            skip_tok.span,
            ast_node.node_id,
        )
        return ast_node, pt_node


    def _parse_aexp(self) -> tuple[Aexp, ParseTreeNode]:
        return self._parse_add_sub()

    def _parse_add_sub(self) -> tuple[Aexp, ParseTreeNode]:
        left_ast, left_pt = self._parse_mul_div()
        while self._peek_kind() in ("PLUS", "MINUS"):
            op_tok = self._advance()
            op_str, rule_name = _CANONICAL_AEXP_OP[op_tok.kind]
            right_ast, right_pt = self._parse_mul_div()
            span = left_ast.span.merge(right_ast.span)
            bin_ast = BinaryAexp(
                op=op_str,
                left=left_ast,
                right=right_ast,
                span=span,
                node_id=self._next_ast_id(),
            )
            bin_pt = self._pt(
                "<вираз>",
                "Aexp",
                rule_name,
                [left_pt, self._leaf(op_tok), right_pt],
                span,
                bin_ast.node_id,
            )
            left_ast, left_pt = bin_ast, bin_pt
        return left_ast, left_pt

    def _parse_mul_div(self) -> tuple[Aexp, ParseTreeNode]:
        left_ast, left_pt = self._parse_aexp_atom()
        while self._peek_kind() in ("MUL", "DIV", "MOD"):
            op_tok = self._advance()
            self._check_strict_token(op_tok)
            op_str, rule_name = _CANONICAL_AEXP_OP[op_tok.kind]
            right_ast, right_pt = self._parse_aexp_atom()
            span = left_ast.span.merge(right_ast.span)
            bin_ast = BinaryAexp(
                op=op_str,
                left=left_ast,
                right=right_ast,
                span=span,
                node_id=self._next_ast_id(),
            )
            bin_pt = self._pt(
                "<вираз>",
                "Aexp",
                rule_name,
                [left_pt, self._leaf(op_tok), right_pt],
                span,
                bin_ast.node_id,
            )
            left_ast, left_pt = bin_ast, bin_pt
        return left_ast, left_pt

    def _parse_aexp_atom(self) -> tuple[Aexp, ParseTreeNode]:
        tok = self._current()
        if tok is None:
            raise self._error(
                "E_SYNTAX_EXPECTED_AEXP",
                "Expected arithmetic expression, reached end of input",
                self._eof_span,
            )

        if tok.kind == "NUM":
            self._advance()
            val = int(tok.value.replace("\u2013", "-").replace("\u2212", "-"))
            ast_node = Number(value=val, span=tok.span, node_id=self._next_ast_id())
            num_pt = self._pt(
                "<число>",
                "Num",
                "NN",
                [self._leaf(tok, ast_node.node_id)],
                tok.span,
                ast_node.node_id,
            )
            aexp_pt = self._pt(
                "<вираз>",
                "Aexp",
                "NA1",
                [num_pt],
                tok.span,
                ast_node.node_id,
            )
            return ast_node, aexp_pt

        if tok.kind == "MINUS":
            nxt = self._current(1)
            if (
                nxt is not None
                and nxt.kind == "NUM"
                and not nxt.value.startswith(("-", "\u2013", "\u2212"))
            ):
                minus_tok = self._advance()
                num_tok = self._advance()
                span = minus_tok.span.merge(num_tok.span)
                val = -int(num_tok.value)
                merged_text = f"-{num_tok.value}"
                merged_tok = Token("NUM", merged_text, span)
                num_ast = Number(value=val, span=span, node_id=self._next_ast_id())
                num_pt = self._pt(
                    "<число>",
                    "Num",
                    "NN",
                    [self._leaf(merged_tok, num_ast.node_id)],
                    span,
                    num_ast.node_id,
                )
                aexp_pt = self._pt(
                    "<вираз>",
                    "Aexp",
                    "NA1",
                    [num_pt],
                    span,
                    num_ast.node_id,
                )
                return num_ast, aexp_pt
            raise self._error(
                "E_SYNTAX_UNARY_MINUS",
                "Unexpected unary '-' before expression",
                tok.span,
                hint="SIPL has no unary '-' operator on variables/expressions; write '0 - <expr>'",
            )

        if tok.kind == "IDENT":
            self._advance()
            var_ast = Variable(name=tok.value, span=tok.span, node_id=self._next_ast_id())
            var_pt = self._pt(
                "<змінна>",
                "Var",
                "NV",
                [self._leaf(tok, var_ast.node_id)],
                tok.span,
                var_ast.node_id,
            )
            aexp_pt = self._pt(
                "<вираз>",
                "Aexp",
                "NA2",
                [var_pt],
                tok.span,
                var_ast.node_id,
            )
            return var_ast, aexp_pt

        if tok.kind == "LPAREN":
            lparen = self._advance()
            inner_ast, inner_pt = self._parse_aexp()
            rparen = self._expect(
                "RPAREN",
                "E_SYNTAX_UNCLOSED_PAREN",
                "closing ')'",
                hint="Add matching ')' for '('",
            )
            span = lparen.span.merge(rparen.span)
            paren_ast = ParenAexp(expr=inner_ast, span=span, node_id=self._next_ast_id())
            aexp_pt = self._pt(
                "<вираз>",
                "Aexp",
                "NA6",
                [self._leaf(lparen), inner_pt, self._leaf(rparen)],
                span,
                paren_ast.node_id,
            )
            return paren_ast, aexp_pt

        raise self._error(
            "E_SYNTAX_EXPECTED_AEXP",
            f"Expected arithmetic expression (number, variable, or '('), found '{tok.value}'",
            tok.span,
        )


    def _parse_bexp(self) -> tuple[Bexp, ParseTreeNode]:
        return self._parse_or_bexp()

    def _parse_or_bexp(self) -> tuple[Bexp, ParseTreeNode]:
        left_ast, left_pt = self._parse_and_bexp()
        while self._peek_kind() == "OR":
            op_tok = self._advance()
            self._check_strict_token(op_tok)
            right_ast, right_pt = self._parse_and_bexp()
            span = left_ast.span.merge(right_ast.span)
            ast_node = BinaryBexp(
                op="or",
                left=left_ast,
                right=right_ast,
                span=span,
                node_id=self._next_ast_id(),
            )
            pt_node = self._pt(
                "<умова>",
                "Bexp",
                "NB3",
                [left_pt, self._leaf(op_tok), right_pt],
                span,
                ast_node.node_id,
            )
            left_ast, left_pt = ast_node, pt_node
        return left_ast, left_pt

    def _parse_and_bexp(self) -> tuple[Bexp, ParseTreeNode]:
        left_ast, left_pt = self._parse_not_bexp()
        while self._peek_kind() == "AND":
            op_tok = self._advance()
            self._check_strict_token(op_tok)
            right_ast, right_pt = self._parse_not_bexp()
            span = left_ast.span.merge(right_ast.span)
            ast_node = BinaryBexp(
                op="and",
                left=left_ast,
                right=right_ast,
                span=span,
                node_id=self._next_ast_id(),
            )
            pt_node = self._pt(
                "<умова>",
                "Bexp",
                "NB_AND",
                [left_pt, self._leaf(op_tok), right_pt],
                span,
                ast_node.node_id,
            )
            left_ast, left_pt = ast_node, pt_node
        return left_ast, left_pt

    def _parse_not_bexp(self) -> tuple[Bexp, ParseTreeNode]:
        if self._peek_kind() == "NOT":
            not_tok = self._advance()
            self._check_strict_token(not_tok)
            operand_ast, operand_pt = self._parse_not_bexp()
            span = not_tok.span.merge(operand_ast.span)
            ast_node = NotBexp(operand=operand_ast, span=span, node_id=self._next_ast_id())
            pt_node = self._pt(
                "<умова>",
                "Bexp",
                "NB4",
                [self._leaf(not_tok), operand_pt],
                span,
                ast_node.node_id,
            )
            return ast_node, pt_node
        return self._parse_bexp_atom()

    def _paren_contains_bexp(self) -> bool:
        """Look ahead inside a balanced '( ... )' to distinguish NB5 from NA6."""
        depth = 0
        idx = self.pos
        while idx < len(self.tokens):
            kind = self.tokens[idx].kind
            if kind == "LPAREN":
                depth += 1
            elif kind == "RPAREN":
                depth -= 1
                if depth == 0:
                    return False
            elif kind in _BEXP_DISAMBIG_KINDS:
                return True
            elif kind in ("KW_THEN", "KW_DO", "SEMICOLON", "KW_END"):
                return False
            idx += 1
        return False

    def _parse_bexp_atom(self) -> tuple[Bexp, ParseTreeNode]:
        tok = self._current()
        if tok is None:
            raise self._error(
                "E_SYNTAX_EXPECTED_BEXP",
                "Expected boolean condition, reached end of input",
                self._eof_span,
            )

        if tok.kind == "LPAREN" and self._paren_contains_bexp():
            lparen = self._advance()
            inner_ast, inner_pt = self._parse_bexp()
            rparen = self._expect(
                "RPAREN",
                "E_SYNTAX_UNCLOSED_PAREN",
                "closing ')' in condition",
                hint="Add matching ')' for '('",
            )
            span = lparen.span.merge(rparen.span)
            ast_node = ParenBexp(cond=inner_ast, span=span, node_id=self._next_ast_id())
            pt_node = self._pt(
                "<умова>",
                "Bexp",
                "NB5",
                [self._leaf(lparen), inner_pt, self._leaf(rparen)],
                span,
                ast_node.node_id,
            )
            return ast_node, pt_node

        return self._parse_compare_bexp()

    def _parse_compare_bexp(self) -> tuple[CompareBexp, ParseTreeNode]:
        left_ast, left_pt = self._parse_aexp()
        cmp_tok = self._current()
        if cmp_tok is None or cmp_tok.kind not in _CANONICAL_CMP_OP:
            found = cmp_tok.value if cmp_tok else "EOF"
            raise self._error(
                "E_SYNTAX_EXPECTED_CMP",
                f"Expected comparison operator ('=', '>', etc.), found '{found}'",
                cmp_tok.span if cmp_tok else self._eof_span,
                hint=(
                    "Boolean conditions in SIPL must compare two arithmetic expressions, "
                    "e.g. 'X > 0' or 'M = N'"
                ),
            )
        self._advance()
        self._check_strict_token(cmp_tok)
        op_str, rule_name = _CANONICAL_CMP_OP[cmp_tok.kind]
        right_ast, right_pt = self._parse_aexp()
        span = left_ast.span.merge(right_ast.span)
        ast_node = CompareBexp(
            op=op_str,
            left=left_ast,
            right=right_ast,
            span=span,
            node_id=self._next_ast_id(),
        )
        pt_node = self._pt(
            "<умова>",
            "Bexp",
            rule_name,
            [left_pt, self._leaf(cmp_tok), right_pt],
            span,
            ast_node.node_id,
        )
        return ast_node, pt_node


def parse_program(source: str, *, strict_bnf: bool = False) -> ParseResult:
    """Parse a SIPL ``source`` string into a typed ``Program`` AST and ``ParseTreeNode``.

    Set ``strict_bnf=True`` to restrict the syntax strictly to the core lecture BNF
    (disallowing ``div``, ``mod``, ``>=``, ``<``, ``<=``, ``!=``, ``and``, etc.).
    """
    tokens = tokenize(source, strict_bnf=strict_bnf)
    parser = _Parser(tokens, source, strict_bnf=strict_bnf)
    ast, parse_tree = parser.parse()
    crown_tokens = parse_tree.crown_tokens()
    crown_text = " ".join(crown_tokens)
    token_values = [t.value for t in tokens]
    is_crown_valid = (
        crown_tokens == token_values
        or "".join(crown_tokens) == "".join(token_values)
    )
    return ParseResult(
        ast=ast,
        parse_tree=parse_tree,
        tokens=tokens,
        crown_text=crown_text,
        is_crown_valid=is_crown_valid,
        source=source,
    )
