# SIPL Language Toolkit (`sipl-toolkit`)

Інструментарій для формальної мови програмування **SIPL** (*SImple Programming Language*) з курсу **«Теорія програмування»**.

Проєкт реалізує повний ланцюжок компіляторного та формально-семантичного аналізу SIPL: формальну EBNF-граматику, лексер, рекурсивний низхідний парсер, конкретне дерево розбору з перевіркою крони, типізований AST, інтерпретатор станів з трасуванням подій, алгебраїчну семантику програми $\mathcal{A}_{\mathrm{SIPL}}$ (побудова термів та покрокове обчислення), автоматизоване індуктивне доведення коректності, інтерактивну візуалізацію (SVG / DOT / HTML5) та CLI.

---

## Задекларовані та реалізовані модулі (Task IDs)

### Задекларований профіль оцінювання (10.0 балів)

| Task ID | Назва модуля / задачі | Бали | Реалізація |
|---|---|---:|---|
| `CORE-02` | Парсер SIPL, конкретне дерево розбору з перевіркою крони та типізований AST | 1.5 | `src/sipl/lexer.py`, `src/sipl/parser.py`, `src/sipl/ast.py` |
| `VIS-01` | Експортери конкретного дерева розбору (Text, JSON, DOT, автономний tidy SVG) | 1.5 | `src/sipl/visualization/exporters.py` |
| `SEM-01` | Алгебра семантичних термів $\mathcal{A}_{\mathrm{SIPL}}$ і покроковий вивід за правилами `NS_*` | 2.0 | `src/sipl/semantics/terms.py` |
| `SEM-02` | Алгебраїчний інтерпретатор термів за формулами `AF_*`, частковість (`↓`/`↑`), Теорема 1.2 | 2.0 | `src/sipl/semantics/evaluator.py` |
| `SEM-04` | Символьний спрощувач, синтез гіпотез `st_k`, пряма/зворотна індукція, контрприклади | 2.5 | `src/sipl/semantics/symbolic.py`, `src/sipl/semantics/prover.py` |
| `REL-02` | Семантичне версіонування, `CHANGELOG.md`, збірка пакету (`.whl`/`.tar.gz`) і тег `v1.0.0` | 0.5 | `CHANGELOG.md`, `pyproject.toml`, `dist/` |
| **Разом** | | **10.0** | |

### Додатково реалізовані модулі інфраструктури та інтеграції

- `CORE-01`: Формальна специфікація BNF/EBNF і діагностики з `SourceSpan` ([grammar/sipl.ebnf](grammar/sipl.ebnf), [grammar/SPECIFICATION.md](grammar/SPECIFICATION.md), `src/sipl/diagnostics.py`).
- `CORE-03` & `CORE-04`: Алгебра станів `A_State = <State; ∇>`, операційний AST-інтерпретатор та структуроване трасування подій (`src/sipl/interpreter/`).
- `CORE-05`: Єдиний CLI `sipl` з 8 підкомандами та підтримкою `--json` (`src/sipl/cli.py`).
- `VIS-02` & `SEM-03`: Експортери AST, інтерактивне порівняння `ParseTree ↔ AST` та 5-панельний синхронізований HTML5-візуалізатор конвеєра (`src/sipl/visualization/exporters.py`).
- `REL-01`: CI-конвеєр GitHub Actions для Linux та Windows ([.github/workflows/ci.yml](.github/workflows/ci.yml)).

---

## Архітектура конвеєра

```text
  SIPL source (.sipl)
         │
         ▼
  lexer.py (Token[]) ──► parser.py (ParseResult)
                              ├──► ParseTreeNode (NP1, NS*, NA*, NB*, NV, NN + crown check)
                              └──► Program AST (Program, Assign, Seq, If, While, Block, Skip)
                                       │
         ┌─────────────────────────────┼─────────────────────────────┐
         ▼                             ▼                             ▼
  interpreter/                  semantics/                    visualization/
  - State (∇, ⊆)                - terms.py (SEM-01: NS_*)     - Text / JSON / DOT / SVG
  - runtime.py (CORE-03/04)     - evaluator.py (SEM-02: AF_*) - ParseTree ↔ AST HTML
                                - symbolic.py + prover.py     - 5-panel Pipeline HTML
                                  (SEM-04: induction & CX)
                                       │
                                       ▼
                                  cli.py (`sipl`)
```

---

## Встановлення

Проєкт не має зовнішніх runtime-залежностей (чиста стандартна бібліотека Python >= 3.11).

### Варіант 1: через `uv` (рекомендовано)

```bash
uv sync --extra dev
uv run sipl --version
```

### Варіант 2: через `pip`

```bash
python -m venv .venv
# Windows PowerShell:
.venv\Scripts\Activate.ps1
# Linux / macOS:
# source .venv/bin/activate

pip install -e ".[dev]"
sipl --version
```

---

## Використання CLI (`sipl`)

### Доступні підкоманди

| Підкоманда | Призначення | Приклад |
|---|---|---|
| `parse` | Розбір програми, друк AST та крони дерева | `sipl parse examples/01_power_xy.sipl` |
| `check` | Валідація синтаксису (`--strict-bnf`) і крони | `sipl check examples/01_power_xy.sipl --strict-bnf` |
| `term` | Побудова семантичного терму (`--format unicode\|latex\|derivation\|json`) | `sipl term examples/01_power_xy.sipl` |
| `eval` | Покрокове обчислення терму в `A_SIPL` | `sipl eval examples/01_power_xy.sipl --state "X=2, Y=5"` |
| `prove` | Індуктивне доведення (`--spec`, `--mode`, `--hypothesis`) | `sipl prove examples/01_power_xy.sipl --spec examples/specs/01_power_xy.json` |
| `visualize` | Генерація SVG, DOT, JSON, `compare-html`, `html` | `sipl visualize examples/01_power_xy.sipl --format html --state "X=2, Y=5" -o out.html` |
| `run` | Виконання AST-інтерпретатором | `sipl run examples/02_div_xy.sipl --state "X=17, Y=5"` |
| `trace` | Трасування подій інтерпретатора | `sipl trace examples/02_div_xy.sipl --state "X=17, Y=5" --json` |

Усі підкоманди підтримують `--strict-bnf` та `--json`.

### Коди завершення (Exit Codes)

- `0`: успішне виконання; для `prove` — коли статус `proved`, `partial` або `unsupported` (не спростовано).
- `1`: синтаксична помилка (`check`/`parse`/тощо), невизначене обчислення `↑` або помилка виконання (`eval`/`run`/`trace`), або статус `disproved` у команді `prove`.

### Приклад запуску: `check` та `eval`

```text
$ sipl check examples/01_power_xy.sipl --strict-bnf
OK: examples/01_power_xy.sipl (leaves=24, crown valid)

$ sipl eval examples/01_power_xy.sipl --state "X=2, Y=5"
Обчислення терму AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))) на початковому стані st = [X ↦ 2, Y ↦ 5].
...
Умова циклу на стані st_5 хибна (false); NumItWH((S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))), st_0) = 5. Результат циклу: st_5 = [X ↦ 2, Y ↦ 0, R ↦ 32].
Результат обчислення: AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st)↓ = st_5 = [X ↦ 2, Y ↦ 0, R ↦ 32].
```

### Приклад запуску: `prove` (коректна та помилкова програми)

```text
$ sipl prove examples/01_power_xy.sipl --spec examples/specs/01_power_xy.json
Статус доведення: proved
...
1. База індукції (k = 0) [proved]: st_k|_{k=0} = [Y ↦ y, X ↦ x, R ↦ 1] = st₀
2. Крок індукції (k → k + 1) [proved]: fs(st_k) = [R ↦ x^(k + 1), Y ↦ y − (k + 1), X ↦ x] = st_{k+1}
3. Умова виходу та завершуваність [proved]: k* = y; st_{k*} = [R ↦ x^y, Y ↦ 0, X ↦ x]
4. Зворотна індукція (st^{k+1} → st^k) [proved]: x_k = x_0; y_k = k + y_0; r_k·x_k^y_k = r_0·x_0^y_0

$ sipl prove examples/invalid/buggy_power_init.sipl --spec examples/specs/01_power_xy.json
Статус доведення: disproved
...
Знайдені контрприклади:
 - st={'Y': 1, 'X': 2}: Постумова 'R = X_0 ^ Y_0' хибна для фінального стану {'Y': 0, 'X': 2, 'R': 0}
```
*(повертає код `1`)*

---


## Демонстраційні артефакти та документація

- [grammar/sipl.ebnf](grammar/sipl.ebnf) — формальна EBNF-граматика SIPL.
- [grammar/SPECIFICATION.md](grammar/SPECIFICATION.md) — правила `NP1`..`NN`, розширення практикуму, пріоритети операторів.
- [docs/DEFENSE_GUIDE.md](docs/DEFENSE_GUIDE.md) — довідник для захисту курсового проєкту (чекліст пп. 10 та 13, теорія, обмеження автоматизації).
- [CHANGELOG.md](CHANGELOG.md) — історія версій SemVer.
- Демонстраційні артефакти в `docs/artifacts/`:
  - `01_power_xy_parse_tree.svg`, `01_power_xy_parse_tree.dot`, `01_power_xy_ast.svg`, `01_power_xy_pipeline.html`, `01_power_xy_proof.md`
  - `02_div_xy_parse_tree.svg`, `02_div_xy_pipeline.html`, `02_div_xy_proof.md`
  - `03_gcd_euclid_parse_tree.svg`, `03_gcd_euclid_pipeline.html`

---

## Перевірка якості та тести

```bash
ruff check src tests
mypy src
pytest -v --cov=sipl --cov-report=term-missing
uv build
```
