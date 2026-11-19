# SIPL Language Specification (`CORE-01`)

**SIPL** (*SImple Programming Language*) is the imperative language formalized in the *Theory of Programming* course (KNU, Faculty of Computer Science and Cybernetics).

This document defines the exact syntax, operator precedence, associativity, lexical rules, and parse-tree rule labels implemented by `sipl-toolkit`.

---

## 1. Course BNF (Strict Mode: `strict_bnf=True`)

From Lecture 1-2 (pp. 4, 10) and Practice 1 (p. 8–9):

| Category | Non-terminal | Meta-var | Production | Rule ID |
|---|---|---|---|---|
| `Prog` | `<програма>` | $P$ | `begin <оператор> end` | `NP1` |
| `Stm` | `<оператор>` | $S$ | `<змінна> := <вираз>` | `NS1` |
| `Stm` | `<оператор>` | $S$ | `<оператор> ; <оператор>` | `NS2` |
| `Stm` | `<оператор>` | $S$ | `if <умова> then <оператор> else <оператор>` | `NS3` |
| `Stm` | `<оператор>` | $S$ | `while <умова> do <оператор>` | `NS4` |
| `Stm` | `<оператор>` | $S$ | `begin <оператор> end` | `NS5` |
| `Stm` | `<оператор>` | $S$ | `skip` | `NS6` |
| `Aexp` | `<вираз>` | $a$ | `<число>` | `NA1` |
| `Aexp` | `<вираз>` | $a$ | `<змінна>` | `NA2` |
| `Aexp` | `<вираз>` | $a$ | `<вираз> + <вираз>` | `NA3` |
| `Aexp` | `<вираз>` | $a$ | `<вираз> - <вираз>` | `NA4` |
| `Aexp` | `<вираз>` | $a$ | `<вираз> * <вираз>` | `NA5` |
| `Aexp` | `<вираз>` | $a$ | `(<вираз>)` | `NA6` |
| `Bexp` | `<умова>` | $b$ | `<вираз> = <вираз>` | `NB1` |
| `Bexp` | `<умова>` | $b$ | `<вираз> > <вираз>` | `NB2` |
| `Bexp` | `<умова>` | $b$ | `<умова> ∨ <умова>` | `NB3` |
| `Bexp` | `<умова>` | $b$ | `¬ <умова>` | `NB4` |
| `Bexp` | `<умова>` | $b$ | `(<умова>)` | `NB5` |
| `Var` | `<змінна>` | $x$ | identifier (`M`, `N`, `R`, `X`, `Y`, ...) | `NV` |
| `Num` | `<число>` | $n$ | integer (`..., -1, 0, 1, 2, 3, ...`) | `NN` |

---

## 2. Workbook Practical Extensions (`strict_bnf=False`, default)

Practice 1–3 and Module Test 1 (Workbook pp. 11, 17–18, 23, 46) also use the following operators, enabled by default when `strict_bnf=False`:

| Category | Construct | Canonical AST Op | Rule ID | Notes |
|---|---|---|---|---|
| `Aexp` | `a1 div a2` | `div` | `NA_DIV` | Integer division |
| `Aexp` | `a1 mod a2` | `mod` | `NA_MOD` | Integer remainder |
| `Bexp` | `a1 >= a2`, `a1 ≥ a2` | `>=` | `NB_GE` | Greater than or equal (`gre`) |
| `Bexp` | `a1 < a2` | `<` | `NB_LT` | Less than (`less`) |
| `Bexp` | `a1 <= a2`, `a1 ≤ a2` | `<=` | `NB_LE` | Less than or equal |
| `Bexp` | `a1 != a2`, `a1 ≠ a2`, `a1 <> a2` | `!=` | `NB_NE` | Not equal |
| `Bexp` | `b1 and b2`, `b1 ∧ b2`, `b1 && b2` | `and` | `NB_AND` | Logical conjunction |

When `strict_bnf=True` is passed to `parse_program`, any extended operator or ASCII logical keyword (`div`, `mod`, `>=`, `<`, `<=`, `!=`, `and`, `or`, `not`, `∧`, `&&`, `||`, `!`, `~`) is rejected with a `SiplSyntaxError`.

---

## 3. Operator Precedence & Associativity

From highest to lowest precedence (Lecture 1-2, p. 8):

| Priority | Operators / Constructs | Associativity | Disambiguation Example |
|---|---|---|---|
| 1 (highest) | `( ... )`, `begin ... end`, `Num`, `Var` | — | Grouping |
| 2 | `*` (`div`, `mod` in extended mode) | Left | `a * b * c` = `(a * b) * c` |
| 3 | `+`, `-` | Left | `a1 - a2 - a3` = `(a1 - a2) - a3` |
| 4 | `=`, `>` (`>=`, `<`, `<=`, `!=` in extended mode) | Non-assoc | Higher precedence than `¬` |
| 5 | `¬` (`not`, `!`, `~`) | Prefix (right) | `while ¬ M = N do` = `while ¬(M = N) do` |
| 6 | `∧` (`and`, `&&` in extended mode) | Left | Between `¬` and `∨` |
| 7 | `∨` (`or`, `\|\|`) | Left | `b1 ∨ b2 ∨ b3` = `(b1 ∨ b2) ∨ b3` |
| 8 | `:=` | — | `x := a` |
| 9 | `while b do S` | — | `while b do S1 ; S2` = `(while b do S1) ; S2` |
| 10 | `if b then S1 else S2` | — | `if b then S1 else S2 ; S3` = `(if b then S1 else S2) ; S3` |
| 11 (lowest) | `;` | Left | `S1 ; S2 ; S3` = `(S1 ; S2) ; S3` |

### Key Disambiguation Rules

1. **Comparisons bind tighter than negation (`¬`)**:
   `¬ M = N` parses as `¬(M = N)`, NOT `(¬M) = N` (which is ill-typed in SIPL anyway since `¬` produces `Bool` and `=` expects `Int`).
2. **Sequential composition (`;`) binds looser than `while` and `if`**:
   - `while b do S1 ; S2` parses as `(while b do S1) ; S2`. To put multiple statements inside a loop or conditional branch, wrap them in `begin ... end` (`NS5`).
   - `if b then S1 else S2 ; S3` parses as `(if b then S1 else S2) ; S3`.
3. **Parentheses in `Bexp` vs `Aexp`**:
   In `( X + 1 ) > Y`, `( X + 1 )` is a parenthesized arithmetic expression (`NA6`) serving as the left operand of `NB2`. In `( X = 1 ) ∨ ( Y = 2 )`, `( X = 1 )` is a parenthesized boolean condition (`NB5`). Because `Aexp` never contains comparison/boolean operators and every `Bexp` contains at least one comparison operator, balanced parenthesized sub-expressions are unambiguously classified.

---

## 4. Lexical Specification

- **Keywords**:
  - Core: `begin`, `end`, `if`, `then`, `else`, `while`, `do`, `skip`
  - Extended (`strict_bnf=False`): `div`, `mod`, `or`, `not`, `and`
- **Identifiers (`Var`)**: `[A-Za-z_][A-Za-z0-9_]*` (case-sensitive, excluding keywords).
- **Integers (`Num`)**: `[0-9]+`, or unary `-`/`–`/`−` followed by `[0-9]+` in unary/expression-start position (e.g., `X := -1`, `(-5)`, `X + -2`, whereas `Y - 1` is binary subtraction `NA4`).
- **Unicode & PDF Copy-Paste Normalization**:
  - Subtraction / unary minus: `-`, `–` (U+2013), `−` (U+2212)
  - Disjunction: `∨` (U+2228), `\uf0da` (Symbol font glyph), `||`, `or`
  - Negation: `¬` (U+00AC), `\uf0d8` (Symbol font glyph), `!`, `~`, `not`
  - Conjunction: `∧` (U+2227), `&&`, `and`
  - Comparisons: `>=` / `≥` (U+2265), `<=` / `≤` (U+2264), `!=` / `≠` (U+2260) / `<>`
- **Comments** (skipped while tracking line/column/offset):
  - Line comments: `// ...` and `# ...`
  - Block comments: `(* ... *)`
- **Whitespace**: spaces, tabs, `\r`, `\n` are skipped while maintaining 1-based line/column and 0-based byte/character offset.
