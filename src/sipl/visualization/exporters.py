"""Exporters and interactive visualizers for SIPL parse trees, ASTs, and semantic pipelines."""

from __future__ import annotations

import html
import json
from collections import defaultdict
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
    ParseTreeNode,
    Program,
    Seq,
    Skip,
    Stm,
    Variable,
    While,
)
from sipl.diagnostics import SourceSpan
from sipl.parser import ParseResult

_PT_CATEGORY_STYLE: dict[str, tuple[str, str, str]] = {
    "Prog": ("#ede9fe", "#7c3aed", "#3b0764"),
    "Stm": ("#dbeafe", "#2563eb", "#1e3a8a"),
    "Aexp": ("#dcfce7", "#16a34a", "#14532d"),
    "Bexp": ("#fef3c7", "#d97706", "#78350f"),
    "Var": ("#cffafe", "#0891b2", "#164e63"),
    "Num": ("#fce7f3", "#db2777", "#831843"),
}
_PT_TERMINAL_STYLE = ("#f1f5f9", "#475569", "#0f172a")

_AST_CATEGORY_STYLE: dict[str, tuple[str, str, str]] = {
    "Prog": ("#ede9fe", "#7c3aed", "#3b0764"),
    "Stm": ("#dbeafe", "#2563eb", "#1e3a8a"),
    "Aexp": ("#dcfce7", "#16a34a", "#14532d"),
    "Bexp": ("#fef3c7", "#d97706", "#78350f"),
}


def _span_short(span: SourceSpan) -> str:
    return f"[{span.start.line}:{span.start.column}]"


def _span_range(span: SourceSpan) -> str:
    return f"[{span.start.line}:{span.start.column}..{span.end.line}:{span.end.column}]"


def _esc_xml(text: str) -> str:
    return html.escape(text, quote=True)


def _esc_dot(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def _strip_xml_decl(svg_text: str) -> str:
    if svg_text.startswith("<?xml"):
        idx = svg_text.find("?>")
        if idx != -1:
            return svg_text[idx + 2 :].lstrip("\r\n")
    return svg_text


def _ast_category(node: ASTNode) -> str:
    if isinstance(node, Program):
        return "Prog"
    if isinstance(node, Stm):
        return "Stm"
    if isinstance(node, Aexp):
        return "Aexp"
    if isinstance(node, Bexp):
        return "Bexp"
    return "Stm"


def _ast_children_and_summary(node: ASTNode) -> tuple[str, list[tuple[str, ASTNode]]]:
    if isinstance(node, Program):
        return ("begin ... end", [("body", node.body)])
    if isinstance(node, Block):
        return ("begin ... end", [("body", node.body)])
    if isinstance(node, Skip):
        return ("skip", [])
    if isinstance(node, Assign):
        return (f"{node.var} :=", [("expr", node.expr)])
    if isinstance(node, Seq):
        return (";", [("left", node.left), ("right", node.right)])
    if isinstance(node, If):
        return (
            "if ... then ... else",
            [("cond", node.cond), ("then", node.then_branch), ("else", node.else_branch)],
        )
    if isinstance(node, While):
        return ("while ... do", [("cond", node.cond), ("body", node.body)])
    if isinstance(node, Number):
        return (str(node.value), [])
    if isinstance(node, Variable):
        return (node.name, [])
    if isinstance(node, BinaryAexp):
        return (f"op: {node.op}", [("left", node.left), ("right", node.right)])
    if isinstance(node, ParenAexp):
        return ("( )", [("expr", node.expr)])
    if isinstance(node, CompareBexp):
        return (f"op: {node.op}", [("left", node.left), ("right", node.right)])
    if isinstance(node, BinaryBexp):
        return (f"op: {node.op}", [("left", node.left), ("right", node.right)])
    if isinstance(node, NotBexp):
        return ("¬", [("operand", node.operand)])
    if isinstance(node, ParenBexp):
        return ("( )", [("cond", node.cond)])
    return ("", [])


@dataclass(slots=True)
class _LayoutNode:
    uid: str
    title_text: str
    subtitle_text: str
    tooltip: str
    fill: str
    stroke: str
    text_color: str
    width: float
    height: float
    children: list[_LayoutNode] = field(default_factory=list)
    attrs: dict[str, str] = field(default_factory=dict)
    edge_label: str = ""
    is_terminal: bool = False
    x: float = 0.0
    y: float = 0.0
    subtree_width: float = 0.0


def _measure_node_box(
    title_text: str, subtitle_text: str, *, is_terminal: bool
) -> tuple[float, float]:
    max_chars = max(len(title_text), len(subtitle_text), 4)
    char_px = 7.4 if not is_terminal else 7.8
    width = max(62.0 if is_terminal else 86.0, min(230.0, max_chars * char_px + 22.0))
    height = 44.0 if subtitle_text else 32.0
    return width, height


def _layout_tree(
    root: _LayoutNode,
    *,
    h_gap: float = 16.0,
    v_gap: float = 52.0,
    margin_x: float = 28.0,
    margin_y: float = 28.0,
) -> tuple[float, float]:
    row_height = 44.0

    def compute_widths(node: _LayoutNode) -> float:
        if not node.children:
            node.subtree_width = node.width
            return node.subtree_width
        child_sum = (
            sum(compute_widths(ch) for ch in node.children)
            + h_gap * (len(node.children) - 1)
        )
        node.subtree_width = max(node.width, child_sum)
        return node.subtree_width

    max_depth = 0

    def assign_coords(node: _LayoutNode, left_x: float, depth: int) -> None:
        nonlocal max_depth
        if depth > max_depth:
            max_depth = depth
        node.y = margin_y + depth * (row_height + v_gap)
        if not node.children:
            node.x = left_x + node.subtree_width / 2.0
            return
        child_sum = sum(ch.subtree_width for ch in node.children) + h_gap * (len(node.children) - 1)
        cursor = left_x + (node.subtree_width - child_sum) / 2.0
        for ch in node.children:
            assign_coords(ch, cursor, depth + 1)
            cursor += ch.subtree_width + h_gap
        mid = (node.children[0].x + node.children[-1].x) / 2.0
        min_cx = left_x + node.width / 2.0
        max_cx = left_x + node.subtree_width - node.width / 2.0
        node.x = max(min_cx, min(max_cx, mid))

    total_w = compute_widths(root)
    assign_coords(root, margin_x, 0)
    canvas_w = total_w + 2.0 * margin_x
    canvas_h = margin_y * 2.0 + (max_depth + 1) * row_height + max_depth * v_gap
    return canvas_w, canvas_h


def _wrap_text_tokens(text: str, max_chars: int) -> list[str]:
    words = text.split(" ")
    lines: list[str] = []
    current = ""
    for word in words:
        candidate = f"{current} {word}".strip() if current else word
        if len(candidate) > max_chars and current:
            lines.append(current)
            current = word
        else:
            current = candidate
    if current:
        lines.append(current)
    return lines or [""]


def _render_layout_svg(
    root: _LayoutNode,
    *,
    svg_id: str,
    title: str,
    footer_lines: list[str] | None = None,
    footer_ok: bool | None = None,
) -> str:
    canvas_w, tree_h = _layout_tree(root)
    min_w = 560.0
    width = max(min_w, canvas_w)
    offset_x = (width - canvas_w) / 2.0

    wrapped_footer: list[str] = []
    if footer_lines:
        max_chars = max(56, int((width - 48.0) / 7.2))
        for line in footer_lines:
            wrapped_footer.extend(_wrap_text_tokens(line, max_chars))

    footer_h = (26.0 + len(wrapped_footer) * 18.0 + 18.0) if wrapped_footer else 0.0
    height = tree_h + footer_h

    edges_svg: list[str] = []
    nodes_svg: list[str] = []

    def walk(node: _LayoutNode) -> None:
        nx = node.x + offset_x
        ny = node.y
        for ch in node.children:
            cx = ch.x + offset_x
            cy = ch.y
            y1 = ny + node.height
            y2 = cy
            ymid = (y1 + y2) / 2.0
            edges_svg.append(
                f'<path class="sipl-edge" d="M {nx:.1f} {y1:.1f} '
                f'C {nx:.1f} {ymid:.1f}, {cx:.1f} {ymid:.1f}, {cx:.1f} {y2:.1f}" '
                f'fill="none" stroke="#94a3b8" stroke-width="1.6"/>'
            )
            if ch.edge_label:
                lx = (nx + cx) / 2.0
                ly = ymid - 4.0
                edges_svg.append(
                    f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" '
                    f'font-family="ui-monospace, Consolas, monospace" font-size="10" '
                    f'fill="#475569">{_esc_xml(ch.edge_label)}</text>'
                )
            walk(ch)

        rx = "10" if node.is_terminal else "6"
        x0 = nx - node.width / 2.0
        attr_str = " ".join(f'{k}="{_esc_xml(v)}"' for k, v in node.attrs.items())
        attr_prefix = f" {attr_str}" if attr_str else ""
        stroke_dash = ' stroke-dasharray="4 2"' if node.is_terminal else ""

        line1_y = ny + (18.0 if node.subtitle_text else 20.0)
        nodes_svg.append(
            f'<g class="sipl-node" data-node-uid="{_esc_xml(node.uid)}"{attr_prefix}>'
            f"<title>{_esc_xml(node.tooltip)}</title>"
            f'<rect x="{x0:.1f}" y="{ny:.1f}" width="{node.width:.1f}" '
            f'height="{node.height:.1f}" rx="{rx}" ry="{rx}" '
            f'fill="{node.fill}" stroke="{node.stroke}" stroke-width="1.6"{stroke_dash}/>'
            f'<text x="{nx:.1f}" y="{line1_y:.1f}" text-anchor="middle" '
            f'font-family="ui-sans-serif, system-ui, -apple-system, sans-serif" '
            f'font-size="12" font-weight="600" fill="{node.text_color}">'
            f"{_esc_xml(node.title_text)}</text>"
            + (
                f'<text x="{nx:.1f}" y="{ny + 34.0:.1f}" text-anchor="middle" '
                f'font-family="ui-monospace, Consolas, monospace" '
                f'font-size="10.5" fill="{node.stroke}">{_esc_xml(node.subtitle_text)}</text>'
                if node.subtitle_text
                else ""
            )
            + "</g>"
        )

    walk(root)

    footer_svg = ""
    if wrapped_footer:
        fy = tree_h + 6.0
        badge_fill = "#dcfce7" if footer_ok else "#fee2e2"
        badge_stroke = "#16a34a" if footer_ok else "#dc2626"
        lines_xml = []
        for idx, line in enumerate(wrapped_footer):
            ly = fy + 22.0 + idx * 18.0
            lines_xml.append(
                f'<text x="24" y="{ly:.1f}" font-family="ui-monospace, Consolas, monospace" '
                f'font-size="11.5" fill="#1e293b">{_esc_xml(line)}</text>'
            )
        footer_svg = (
            f'<g class="sipl-crown-footer">'
            f'<rect x="14" y="{fy:.1f}" width="{width - 28.0:.1f}" height="{footer_h - 14.0:.1f}" '
            f'rx="8" ry="8" fill="{badge_fill}" stroke="{badge_stroke}" stroke-width="1.2"/>'
            + "".join(lines_xml)
            + "</g>"
        )

    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        f'<svg id="{_esc_xml(svg_id)}" xmlns="http://www.w3.org/2000/svg" '
        f'width="{width:.0f}" height="{height:.0f}" viewBox="0 0 {width:.0f} {height:.0f}">\n'
        f"<title>{_esc_xml(title)}</title>\n"
        f'<rect width="100%" height="100%" fill="#ffffff"/>\n'
        f'<g class="sipl-edges">{"".join(edges_svg)}</g>\n'
        f'<g class="sipl-nodes">{"".join(nodes_svg)}</g>\n'
        f"{footer_svg}\n"
        "</svg>"
    )


def render_parse_tree_text(result: ParseResult) -> str:
    """Render an indented parse tree with non-terminals, rules, leaf numbers, spans, and crown."""
    lines: list[str] = ["Parse Tree (SIPL):"]

    def visit(node: ParseTreeNode, prefix: str, is_last: bool, is_root: bool) -> None:
        connector = "" if is_root else ("└── " if is_last else "├── ")
        span_txt = _span_short(node.span)
        if node.is_terminal:
            leaf_no = node.leaf_index if node.leaf_index is not None else "?"
            tok = node.token_text if node.token_text is not None else node.label
            ast_suffix = f" ({node.ast_node_id})" if node.ast_node_id else ""
            lines.append(f"{prefix}{connector}[{leaf_no}] '{tok}' {span_txt}{ast_suffix}")
        else:
            rule_part = f" [{node.rule_name}]" if node.rule_name else ""
            ast_part = f" ({node.ast_node_id})" if node.ast_node_id else ""
            lines.append(f"{prefix}{connector}{node.label}{rule_part} {span_txt}{ast_part}")

        child_prefix = "" if is_root else prefix + ("    " if is_last else "│   ")
        for idx, child in enumerate(node.children):
            visit(child, child_prefix, idx == len(node.children) - 1, False)

    visit(result.parse_tree, "", True, True)
    lines.append("")
    lines.append(f"Крона дерева: {result.crown_text}")
    lines.append(f"Нумерована крона: {result.parse_tree.numbered_crown()}")
    status = "OK" if result.is_crown_valid else "MISMATCH"
    lines.append(f"Синтаксична перевірка крони дерева: {status}")
    return "\n".join(lines)


def render_parse_tree_json(result: ParseResult) -> str:
    """Serialize parse tree, crown text, and crown validity check as structured JSON."""
    payload: dict[str, Any] = {
        "crown_text": result.crown_text,
        "numbered_crown": result.parse_tree.numbered_crown(),
        "is_crown_valid": result.is_crown_valid,
        "leaf_count": len(result.parse_tree.leaves()),
        "tree": result.parse_tree.to_dict(),
    }
    return json.dumps(payload, ensure_ascii=False, indent=2)


def render_parse_tree_dot(result: ParseResult) -> str:
    """Render the concrete parse tree as a Graphviz DOT ``digraph SIPLParseTree``."""
    lines: list[str] = [
        "digraph SIPLParseTree {",
        '  rankdir=TB;',
        '  node [fontname="Helvetica", fontsize=11];',
        '  edge [color="#64748b"];',
    ]

    def visit(node: ParseTreeNode) -> None:
        span_txt = _span_short(node.span)
        if node.is_terminal:
            leaf_no = node.leaf_index if node.leaf_index is not None else "?"
            tok = node.token_text if node.token_text is not None else node.label
            fill, stroke, _ = _PT_TERMINAL_STYLE
            label = f"[{leaf_no}] {tok}\\n{span_txt}"
            lines.append(
                f'  {node.node_id} [label="{_esc_dot(label)}", '
                f'shape=box, style="rounded,filled", fillcolor="{fill}", color="{stroke}"];'
            )
        else:
            fill, stroke, _ = _PT_CATEGORY_STYLE.get(
                node.category or "", ("#f8fafc", "#475569", "#0f172a")
            )
            rule_part = f"\\n[{node.rule_name}]" if node.rule_name else ""
            label = f"{node.label}{rule_part}\\n{span_txt}"
            lines.append(
                f'  {node.node_id} [label="{_esc_dot(label)}", '
                f'shape=ellipse, style="filled", fillcolor="{fill}", color="{stroke}"];'
            )

        for child in node.children:
            lines.append(f"  {node.node_id} -> {child.node_id};")
            visit(child)

    visit(result.parse_tree)
    lines.append("}")
    return "\n".join(lines)


def _build_pt_layout(node: ParseTreeNode, inherited_ast_id: str | None = None) -> _LayoutNode:
    owner_ast_id = node.ast_node_id or inherited_ast_id
    span_str = _span_range(node.span)
    attrs: dict[str, str] = {
        "data-pt-id": node.node_id,
        "data-span": span_str,
    }
    if owner_ast_id:
        attrs["data-ast-id"] = owner_ast_id

    if node.is_terminal:
        leaf_no = node.leaf_index if node.leaf_index is not None else "?"
        tok = node.token_text if node.token_text is not None else node.label
        title_text = tok
        subtitle_text = f"[{leaf_no}] {_span_short(node.span)}"
        fill, stroke, text_color = _PT_TERMINAL_STYLE
        tooltip = f"Terminal [{leaf_no}] '{tok}' | Span {span_str}"
        if owner_ast_id:
            tooltip += f" | AST: {owner_ast_id}"
        attrs["data-leaf-index"] = str(leaf_no)
        w, h = _measure_node_box(title_text, subtitle_text, is_terminal=True)
        return _LayoutNode(
            uid=node.node_id,
            title_text=title_text,
            subtitle_text=subtitle_text,
            tooltip=tooltip,
            fill=fill,
            stroke=stroke,
            text_color=text_color,
            width=w,
            height=h,
            attrs=attrs,
            is_terminal=True,
        )

    title_text = node.label
    subtitle_text = node.rule_name or (node.category or "")
    fill, stroke, text_color = _PT_CATEGORY_STYLE.get(
        node.category or "", ("#f8fafc", "#475569", "#0f172a")
    )
    tooltip = f"{node.label} [{node.rule_name or '?'}] | Span {span_str}"
    if node.ast_node_id:
        tooltip += f" | AST: {node.ast_node_id}"
    w, h = _measure_node_box(title_text, subtitle_text, is_terminal=False)
    children = [_build_pt_layout(ch, owner_ast_id) for ch in node.children]
    return _LayoutNode(
        uid=node.node_id,
        title_text=title_text,
        subtitle_text=subtitle_text,
        tooltip=tooltip,
        fill=fill,
        stroke=stroke,
        text_color=text_color,
        width=w,
        height=h,
        children=children,
        attrs=attrs,
        is_terminal=False,
    )


def render_parse_tree_svg(result: ParseResult) -> str:
    """Render a standalone, tidy-layout XML SVG of the concrete SIPL parse tree."""
    layout_root = _build_pt_layout(result.parse_tree)
    status = "OK" if result.is_crown_valid else "MISMATCH"
    footer = [
        f"Крона дерева: {result.parse_tree.numbered_crown()}",
        f"Синтаксична перевірка крони дерева: {status}",
    ]
    return _render_layout_svg(
        layout_root,
        svg_id="sipl-parse-tree-svg",
        title="SIPL Concrete Parse Tree",
        footer_lines=footer,
        footer_ok=result.is_crown_valid,
    )


def render_ast_text(result: ParseResult) -> str:
    """Render an indented textual view of the typed SIPL AST."""
    lines: list[str] = ["Abstract Syntax Tree (SIPL):"]

    def visit(node: ASTNode, edge_label: str, prefix: str, is_last: bool, is_root: bool) -> None:
        connector = "" if is_root else ("└── " if is_last else "├── ")
        edge_prefix = f"{edge_label}: " if edge_label else ""
        summary, children = _ast_children_and_summary(node)
        summary_part = f" ({summary})" if summary else ""
        lines.append(
            f"{prefix}{connector}{edge_prefix}{node.__class__.__name__}"
            f"{summary_part} [{node.node_id}] {_span_short(node.span)}"
        )
        child_prefix = "" if is_root else prefix + ("    " if is_last else "│   ")
        for idx, (lbl, child) in enumerate(children):
            visit(child, lbl, child_prefix, idx == len(children) - 1, False)

    visit(result.ast, "", "", True, True)
    return "\n".join(lines)


def render_ast_json(result: ParseResult) -> str:
    """Serialize the typed SIPL AST into structured JSON."""
    return json.dumps(result.ast.to_dict(), ensure_ascii=False, indent=2)


def render_ast_dot(result: ParseResult) -> str:
    """Render the typed SIPL AST as a Graphviz DOT ``digraph SIPLAST``."""
    lines: list[str] = [
        "digraph SIPLAST {",
        "  rankdir=TB;",
        '  node [fontname="Helvetica", fontsize=11];',
        '  edge [color="#64748b", fontsize=10, fontname="Helvetica"];',
    ]

    def visit(node: ASTNode) -> None:
        summary, children = _ast_children_and_summary(node)
        cat = _ast_category(node)
        fill, stroke, _ = _AST_CATEGORY_STYLE.get(cat, ("#f8fafc", "#475569", "#0f172a"))
        summary_part = f"\\n{summary}" if summary else ""
        label = (
            f"{node.__class__.__name__}{summary_part}\\n"
            f"[{node.node_id}] {_span_short(node.span)}"
        )
        lines.append(
            f'  {node.node_id} [label="{_esc_dot(label)}", '
            f'shape=box, style="rounded,filled", fillcolor="{fill}", color="{stroke}"];'
        )
        for edge_lbl, child in children:
            lines.append(f'  {node.node_id} -> {child.node_id} [label="{_esc_dot(edge_lbl)}"];')
            visit(child)

    visit(result.ast)
    lines.append("}")
    return "\n".join(lines)


def _build_ast_layout(node: ASTNode, edge_label: str = "") -> _LayoutNode:
    summary, children = _ast_children_and_summary(node)
    cat = _ast_category(node)
    fill, stroke, text_color = _AST_CATEGORY_STYLE.get(cat, ("#f8fafc", "#475569", "#0f172a"))
    title_text = node.__class__.__name__
    subtitle_text = f"{summary} ({node.node_id})" if summary else node.node_id
    span_str = _span_range(node.span)
    tooltip = f"{node.__class__.__name__} ({node.node_id}) | {summary} | Span {span_str}"
    w, h = _measure_node_box(title_text, subtitle_text, is_terminal=False)
    child_layouts = [_build_ast_layout(ch, lbl) for lbl, ch in children]
    return _LayoutNode(
        uid=node.node_id,
        title_text=title_text,
        subtitle_text=subtitle_text,
        tooltip=tooltip,
        fill=fill,
        stroke=stroke,
        text_color=text_color,
        width=w,
        height=h,
        children=child_layouts,
        attrs={
            "data-ast-id": node.node_id,
            "data-span": span_str,
        },
        edge_label=edge_label,
        is_terminal=False,
    )


def render_ast_svg(result: ParseResult) -> str:
    """Render a standalone, tidy-layout XML SVG of the typed SIPL AST."""
    layout_root = _build_ast_layout(result.ast)
    return _render_layout_svg(
        layout_root,
        svg_id="sipl-ast-svg",
        title="SIPL Abstract Syntax Tree",
    )


def compare_parse_tree_and_ast(result: ParseResult) -> dict[str, Any]:
    """Compare concrete Parse Tree and typed AST structures, depth, mapping, and dropped tokens."""
    pt_total = 0
    pt_nonterminals = 0
    pt_terminals = 0
    pt_max_depth = 0
    ast_to_pt: dict[str, list[str]] = defaultdict(list)
    removed_tokens: list[dict[str, Any]] = []
    collapsed_rules: list[dict[str, str]] = []

    def walk_pt(node: ParseTreeNode, depth: int) -> None:
        nonlocal pt_total, pt_nonterminals, pt_terminals, pt_max_depth
        pt_total += 1
        if depth > pt_max_depth:
            pt_max_depth = depth
        if node.ast_node_id is not None:
            ast_to_pt[node.ast_node_id].append(node.node_id)

        if node.is_terminal:
            pt_terminals += 1
            if node.ast_node_id is None:
                tok = node.token_text if node.token_text is not None else node.label
                removed_tokens.append(
                    {
                        "leaf_index": node.leaf_index,
                        "token": tok,
                        "span": node.span.to_dict(),
                        "pt_node_id": node.node_id,
                    }
                )
        else:
            pt_nonterminals += 1
            if len(node.children) == 1 and node.rule_name in ("NA1", "NA2", "NV", "NN"):
                collapsed_rules.append(
                    {
                        "pt_node_id": node.node_id,
                        "rule_name": node.rule_name,
                        "label": node.label,
                        "ast_node_id": node.ast_node_id or "",
                    }
                )
        for ch in node.children:
            walk_pt(ch, depth + 1)

    walk_pt(result.parse_tree, 1)

    ast_total = 0
    ast_max_depth = 0
    ast_ids: list[str] = []

    def walk_ast(node: ASTNode, depth: int) -> None:
        nonlocal ast_total, ast_max_depth
        ast_total += 1
        if depth > ast_max_depth:
            ast_max_depth = depth
        ast_ids.append(node.node_id)
        _, children = _ast_children_and_summary(node)
        for _, ch in children:
            walk_ast(ch, depth + 1)

    walk_ast(result.ast, 1)

    for aid in ast_ids:
        ast_to_pt.setdefault(aid, [])

    reduction_pct = (
        round((pt_total - ast_total) / pt_total * 100.0, 1) if pt_total > 0 else 0.0
    )

    return {
        "parse_tree_node_count": pt_total,
        "parse_tree_nonterminal_count": pt_nonterminals,
        "parse_tree_terminal_count": pt_terminals,
        "parse_tree_depth": pt_max_depth,
        "ast_node_count": ast_total,
        "ast_depth": ast_max_depth,
        "node_reduction_count": pt_total - ast_total,
        "node_reduction_percent": reduction_pct,
        "ast_to_parse_tree_ids": dict(ast_to_pt),
        "removed_concrete_tokens": removed_tokens,
        "removed_token_texts": [item["token"] for item in removed_tokens],
        "collapsed_chain_rules": collapsed_rules,
    }


def _build_interactive_source_html(result: ParseResult) -> str:
    """Render ``result.source`` with token spans carrying ``data-ast-id`` and ``data-ancestors``."""
    leaf_meta: list[tuple[int, int, str, str, int | None, list[str]]] = []

    def walk(node: ParseTreeNode, inherited_ast: str | None, ancestors: list[str]) -> None:
        owner = node.ast_node_id or inherited_ast
        next_ancestors = list(ancestors)
        if node.ast_node_id and (not next_ancestors or next_ancestors[-1] != node.ast_node_id):
            next_ancestors.append(node.ast_node_id)

        if node.is_terminal:
            start = node.span.start.offset
            end = node.span.end.offset
            if end > start and end <= len(result.source):
                leaf_meta.append(
                    (
                        start,
                        end,
                        owner or "",
                        node.node_id,
                        node.leaf_index,
                        next_ancestors,
                    )
                )
            return
        for ch in node.children:
            walk(ch, owner, next_ancestors)

    walk(result.parse_tree, None, [])
    leaf_meta.sort(key=lambda item: item[0])

    parts: list[str] = []
    cursor = 0
    src = result.source
    for start, end, owner_ast, pt_id, leaf_idx, anc in leaf_meta:
        if start < cursor:
            continue
        if start > cursor:
            parts.append(_esc_xml(src[cursor:start]))
        tok_text = src[start:end]
        anc_str = ",".join(dict.fromkeys(anc))
        leaf_attr = f' data-leaf-index="{leaf_idx}"' if leaf_idx is not None else ""
        parts.append(
            f'<span class="src-tok" data-ast-id="{_esc_xml(owner_ast)}" '
            f'data-pt-id="{_esc_xml(pt_id)}"{leaf_attr} '
            f'data-ancestors="{_esc_xml(anc_str)}">{_esc_xml(tok_text)}</span>'
        )
        cursor = end

    if cursor < len(src):
        parts.append(_esc_xml(src[cursor:]))

    rendered = "".join(parts)
    numbered_lines: list[str] = []
    for idx, line_html in enumerate(rendered.split("\n"), start=1):
        numbered_lines.append(
            f'<div class="src-line"><span class="ln">{idx:>3}</span>'
            f'<span class="lc">{line_html}</span></div>'
        )
    return "".join(numbered_lines)


_SHARED_HTML_CSS = """
:root {
  --bg: #f8fafc;
  --card: #ffffff;
  --border: #cbd5e1;
  --text: #0f172a;
  --muted: #475569;
  --accent: #2563eb;
  --accent-bg: #dbeafe;
  --hl-bg: #fef08a;
  --hl-stroke: #ea580c;
}
* { box-sizing: border-box; }
body {
  margin: 0; padding: 16px 20px;
  font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, sans-serif;
  background: var(--bg); color: var(--text); line-height: 1.45;
}
header.topbar {
  display: flex; flex-wrap: wrap; align-items: center; justify-content: space-between;
  gap: 12px; margin-bottom: 14px; padding: 12px 16px;
  background: var(--card); border: 1px solid var(--border); border-radius: 10px;
}
header.topbar h1 { margin: 0; font-size: 18px; }
.badges { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; }
.badge {
  display: inline-block; padding: 3px 10px; border-radius: 999px;
  font-size: 12px; font-weight: 600; border: 1px solid var(--border); background: #f1f5f9;
}
.badge.ok { background: #dcfce7; border-color: #16a34a; color: #14532d; }
.badge.err { background: #fee2e2; border-color: #dc2626; color: #7f1d1d; }
.selection-bar {
  display: flex; flex-wrap: wrap; align-items: center; justify-content: space-between;
  gap: 10px; margin-bottom: 14px; padding: 8px 14px;
  background: #eff6ff; border: 1px solid #93c5fd; border-radius: 8px; font-size: 13px;
}
.selection-bar button {
  padding: 4px 10px; border: 1px solid #93c5fd; border-radius: 6px;
  background: #ffffff; cursor: pointer; font-size: 12px;
}
.grid-2 { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 14px; }
.grid-pipeline { display: grid; grid-template-columns: 1fr 1fr; gap: 14px; }
@media (max-width: 1024px) { .grid-2, .grid-pipeline { grid-template-columns: 1fr; } }
.panel {
  background: var(--card); border: 1px solid var(--border); border-radius: 10px;
  display: flex; flex-direction: column; overflow: hidden;
}
.panel.full { grid-column: 1 / -1; }
.panel-head {
  padding: 9px 14px; border-bottom: 1px solid var(--border); background: #f1f5f9;
  font-weight: 600; font-size: 14px; display: flex;
  justify-content: space-between; align-items: center;
}
.panel-body { padding: 12px 14px; overflow: auto; }
.svg-wrap {
  overflow: auto; max-height: 540px; border: 1px solid #e2e8f0;
  border-radius: 6px; background: #fff;
}
.src-code {
  font-family: ui-monospace, SFMono-Regular, Consolas, monospace; font-size: 13px;
  background: #0f172a; color: #e2e8f0; padding: 10px 12px; border-radius: 8px; overflow-x: auto;
}
.src-line { white-space: pre; min-height: 1.45em; }
.src-line .ln { color: #64748b; user-select: none; margin-right: 12px; }
.src-tok { cursor: pointer; border-radius: 3px; padding: 0 1px; transition: background 0.12s; }
.src-tok:hover { background: rgba(59, 130, 246, 0.35); }
.src-tok.is-highlighted { background: #facc15; color: #0f172a; font-weight: 700; }
.sipl-node { cursor: pointer; }
.sipl-node:hover rect { stroke-width: 2.5; }
.sipl-node.is-highlighted rect {
  fill: var(--hl-bg) !important; stroke: var(--hl-stroke) !important; stroke-width: 3 !important;
}
table.sipl-table { width: 100%; border-collapse: collapse; font-size: 12.5px; }
table.sipl-table th, table.sipl-table td {
  border: 1px solid #e2e8f0; padding: 6px 8px; text-align: left; vertical-align: top;
}
table.sipl-table th { background: #f8fafc; font-weight: 600; }
tr[data-ast-id] { cursor: pointer; }
tr[data-ast-id]:hover { background: #f1f5f9; }
tr.is-highlighted { background: #fef9c3 !important; outline: 2px solid #eab308; }
pre.formula {
  margin: 4px 0 10px 0; padding: 8px 10px; background: #f8fafc;
  border: 1px solid #e2e8f0; border-radius: 6px;
  font-family: ui-monospace, Consolas, monospace; font-size: 12.5px; overflow-x: auto;
}
.muted { color: var(--muted); font-size: 13px; }
"""

_SHARED_HIGHLIGHT_JS = """
(function() {
  const infoEl = document.getElementById('sipl-selection-info');
  const clearBtn = document.getElementById('sipl-clear-selection');

  function clearHighlights() {
    document.querySelectorAll('.is-highlighted').forEach(
      el => el.classList.remove('is-highlighted')
    );
    if (infoEl) {
      infoEl.textContent =
        'Click any Source token, Parse Tree node, AST node, or step to highlight.';
    }
  }

  function highlightSelection(astId, ptId, label) {
    clearHighlights();
    let count = 0;

    if (astId) {
      document.querySelectorAll('[data-ast-id="' + CSS.escape(astId) + '"]').forEach(el => {
        el.classList.add('is-highlighted');
        count++;
      });
      document.querySelectorAll('.src-tok').forEach(tok => {
        const anc = (tok.getAttribute('data-ancestors') || '').split(',');
        if (anc.includes(astId)) {
          tok.classList.add('is-highlighted');
        }
      });
    }

    if (ptId) {
      document.querySelectorAll('[data-pt-id="' + CSS.escape(ptId) + '"]').forEach(el => {
        el.classList.add('is-highlighted');
        count++;
      });
    }

    if (infoEl) {
      const parts = [];
      if (astId) parts.push('AST: ' + astId);
      if (ptId) parts.push('PT: ' + ptId);
      if (label) parts.push(label);
      infoEl.textContent = parts.length ? ('Selected -> ' + parts.join(' | ')) : 'No linked node.';
    }
  }

  document.addEventListener('click', function(ev) {
    const node = ev.target.closest('.sipl-node, .src-tok, tr[data-ast-id]');
    if (!node) return;
    const astId = node.getAttribute('data-ast-id') || '';
    const ptId = node.getAttribute('data-pt-id') || '';
    const titleNode = node.querySelector('title');
    const label = titleNode ? titleNode.textContent : (node.textContent || '').trim().slice(0, 60);
    highlightSelection(astId, ptId, label);
  });

  if (clearBtn) {
    clearBtn.addEventListener('click', clearHighlights);
  }
  document.addEventListener('keydown', function(ev) {
    if (ev.key === 'Escape') clearHighlights();
  });
})();
"""


def render_comparison_html(result: ParseResult) -> str:
    """Render a side-by-side interactive SVG/HTML comparison of Parse Tree vs AST."""
    cmp_data = compare_parse_tree_and_ast(result)
    pt_svg = _strip_xml_decl(render_parse_tree_svg(result))
    ast_svg = _strip_xml_decl(render_ast_svg(result))
    source_html = _build_interactive_source_html(result)
    crown_cls = "ok" if result.is_crown_valid else "err"
    crown_status = "OK" if result.is_crown_valid else "MISMATCH"
    dropped_tokens = ", ".join(cmp_data["removed_token_texts"]) or "(none)"

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1.0"/>
  <title>SIPL Parse Tree vs AST Comparison</title>
  <style>{_SHARED_HTML_CSS}</style>
</head>
<body>
  <header class="topbar">
    <h1>SIPL Parse Tree &harr; AST Comparison</h1>
    <div class="badges">
      <span class="badge {crown_cls}">Crown Check: {crown_status}</span>
      <span class="badge">
        Parse Tree Nodes: {cmp_data['parse_tree_node_count']} (depth {cmp_data['parse_tree_depth']})
      </span>
      <span class="badge">
        AST Nodes: {cmp_data['ast_node_count']} (depth {cmp_data['ast_depth']})
      </span>
      <span class="badge">
        Reduction: -{cmp_data['node_reduction_count']} ({cmp_data['node_reduction_percent']}%)
      </span>
    </div>
  </header>

  <div class="selection-bar">
    <span id="sipl-selection-info">
      Click any Source token, Parse Tree node, or AST node to synchronize highlights.
    </span>
    <button id="sipl-clear-selection" type="button">Clear (Esc)</button>
  </div>

  <section class="panel" style="margin-bottom: 14px;">
    <div class="panel-head">
      <span>Source Program &amp; Dropped Concrete Tokens</span>
      <span class="muted">Concrete tokens omitted as AST nodes: {_esc_xml(dropped_tokens)}</span>
    </div>
    <div class="panel-body">
      <div class="src-code">{source_html}</div>
    </div>
  </section>

  <div class="grid-2">
    <section class="panel">
      <div class="panel-head">
        <span>Concrete Parse Tree (Practice 1)</span>
        <span class="muted">{cmp_data['parse_tree_terminal_count']} leaves</span>
      </div>
      <div class="panel-body">
        <div class="svg-wrap">{pt_svg}</div>
      </div>
    </section>

    <section class="panel">
      <div class="panel-head">
        <span>Typed Abstract Syntax Tree (AST)</span>
        <span class="muted">{cmp_data['ast_node_count']} nodes</span>
      </div>
      <div class="panel-body">
        <div class="svg-wrap">{ast_svg}</div>
      </div>
    </section>
  </div>

  <script>{_SHARED_HIGHLIGHT_JS}</script>
</body>
</html>"""


def _get_attr_or_key(obj: Any, *names: str, default: Any = None) -> Any:
    if obj is None:
        return default
    for name in names:
        if isinstance(obj, dict) and name in obj:
            return obj[name]
        if hasattr(obj, name):
            val = getattr(obj, name)
            if val is not None:
                return val
    return default


def _call_or_attr(obj: Any, method_name: str, *attr_names: str, default: Any = None) -> Any:
    if obj is None:
        return default
    fn = getattr(obj, method_name, None)
    if callable(fn):
        return fn()
    return _get_attr_or_key(obj, *attr_names, default=default)


def _to_dict_safe(obj: Any) -> dict[str, Any]:
    if obj is None:
        return {}
    if isinstance(obj, dict):
        return obj
    fn = getattr(obj, "to_dict", None)
    if callable(fn):
        res = fn()
        if isinstance(res, dict):
            return res
    return {}


def _format_state_display(state_obj: Any) -> str:
    if state_obj is None:
        return "⊥ (undefined)"
    if isinstance(state_obj, bool):
        return "true" if state_obj else "false"
    fn = getattr(state_obj, "format_course", None)
    if callable(fn):
        return str(fn())
    if isinstance(state_obj, dict):
        inner = ", ".join(f"{k} ↦ {v}" for k, v in state_obj.items())
        return f"[{inner}]"
    return str(state_obj)


def _extract_semantic_info(semantic_term: Any | None) -> dict[str, Any]:
    if semantic_term is None:
        return {"present": False}
    data = _to_dict_safe(semantic_term)
    unicode_str = _call_or_attr(
        semantic_term, "format_unicode", "unicode", "term_unicode", "text"
    ) or data.get("unicode") or data.get("term_unicode")
    if unicode_str is None and not isinstance(semantic_term, dict):
        unicode_str = str(semantic_term)
    latex_str = _call_or_attr(
        semantic_term, "format_latex", "latex", "term_latex"
    ) or data.get("latex") or data.get("term_latex")

    raw_steps = (
        _get_attr_or_key(semantic_term, "derivation_steps", "steps", "trace")
        or data.get("derivation_steps")
        or data.get("steps")
        or []
    )
    steps: list[dict[str, str]] = []
    for idx, st in enumerate(raw_steps, start=1):
        st_dict = _to_dict_safe(st)
        rule = str(
            _get_attr_or_key(st, "rule", "rule_id", "rule_name")
            or st_dict.get("rule")
            or st_dict.get("rule_name")
            or f"Step {idx}"
        )
        ast_id = str(
            _get_attr_or_key(st, "ast_node_id", "node_id")
            or st_dict.get("ast_node_id")
            or st_dict.get("node_id")
            or ""
        )
        fragment = str(
            _get_attr_or_key(
                st, "source_fragment", "source_form", "fragment", "program_fragment", "stm"
            )
            or st_dict.get("source_fragment")
            or st_dict.get("source_form")
            or st_dict.get("fragment")
            or ""
        )
        term_txt = str(
            _call_or_attr(
                st,
                "format_unicode",
                "term",
                "semantic_term",
                "term_unicode",
                "target_form",
                "formula",
            )
            or st_dict.get("term")
            or st_dict.get("term_unicode")
            or st_dict.get("target_form")
            or ""
        )
        note_val = (
            _get_attr_or_key(st, "explanation", "description", "note")
            or st_dict.get("explanation")
            or ""
        )
        if not note_val:
            unifier = _get_attr_or_key(st, "unifier") or st_dict.get("unifier")
            if isinstance(unifier, dict) and unifier:
                note_val = ", ".join(f"{k} ↦ {v}" for k, v in unifier.items())
        note = str(note_val)
        steps.append(
            {
                "index": str(idx),
                "rule": rule,
                "ast_node_id": ast_id,
                "fragment": fragment,
                "term": term_txt,
                "note": note,
            }
        )

    return {
        "present": True,
        "unicode": str(unicode_str or ""),
        "latex": str(latex_str or ""),
        "steps": steps,
    }


def _extract_eval_info(eval_result: Any | None) -> dict[str, Any]:
    if eval_result is None:
        return {"present": False}
    data = _to_dict_safe(eval_result)
    is_def = _get_attr_or_key(eval_result, "is_defined", "defined", default=True)
    status = str(
        _get_attr_or_key(eval_result, "status")
        or data.get("status")
        or ("finished" if is_def else "undefined")
    )
    initial_state = _get_attr_or_key(eval_result, "initial_state") or data.get("initial_state")
    final_state = _get_attr_or_key(eval_result, "final_state") or data.get("final_state")
    error_msg = (
        _get_attr_or_key(eval_result, "error", "undefined_reason")
        or data.get("error")
        or data.get("undefined_reason")
    )

    raw_steps = (
        _get_attr_or_key(eval_result, "steps", "af_steps", "derivation_steps")
        or data.get("steps")
        or data.get("af_steps")
    )
    rows: list[dict[str, str]] = []
    if raw_steps:
        for idx, st in enumerate(raw_steps, start=1):
            st_dict = _to_dict_safe(st)
            step_no = str(
                _get_attr_or_key(st, "step", "step_index")
                or st_dict.get("step")
                or st_dict.get("step_index")
                or idx
            )
            rule = str(
                _get_attr_or_key(st, "rule", "rule_id", "rule_name", "formula_name", "operation")
                or st_dict.get("rule")
                or st_dict.get("formula_name")
                or "AF"
            )
            ast_id = str(
                _get_attr_or_key(st, "ast_node_id", "node_id")
                or st_dict.get("ast_node_id")
                or st_dict.get("node_id")
                or ""
            )
            detail = str(
                _get_attr_or_key(
                    st, "formula", "explanation", "description", "condition", "expression_text"
                )
                or st_dict.get("formula")
                or st_dict.get("explanation")
                or st_dict.get("expression_text")
                or ""
            )
            st_state = _get_attr_or_key(st, "after_state", "state", "output_state")
            if st_state is None:
                st_state = st_dict.get("after_state", st_dict.get("state"))
            if st_state is None:
                st_state = _get_attr_or_key(st, "output_value")
                if st_state is None and "output_value" in st_dict:
                    st_state = st_dict["output_value"]
            if st_state is None and rule == "AF_SEQ":
                state_display = "→ (decompose)"
            elif st_state is None:
                state_display = "↑ (undefined)"
            else:
                state_display = _format_state_display(st_state)
            rows.append(
                {
                    "step": step_no,
                    "rule": rule,
                    "ast_node_id": ast_id,
                    "detail": detail,
                    "state": state_display,
                }
            )
    else:
        trace = _get_attr_or_key(eval_result, "trace")
        events = (
            _get_attr_or_key(trace, "events")
            if trace is not None
            else data.get("trace", {}).get("events")
        )
        for idx, ev in enumerate(events or [], start=1):
            ev_dict = _to_dict_safe(ev)
            ev_type = str(_get_attr_or_key(ev, "event_type") or ev_dict.get("event_type") or "")
            stmt_kind = str(
                _get_attr_or_key(ev, "statement_kind") or ev_dict.get("statement_kind") or ""
            )
            details = _get_attr_or_key(ev, "details") or ev_dict.get("details") or {}
            rows.append(
                {
                    "step": str(_get_attr_or_key(ev, "step") or ev_dict.get("step") or idx),
                    "rule": f"{ev_type} ({stmt_kind})" if stmt_kind else ev_type,
                    "ast_node_id": str(
                        _get_attr_or_key(ev, "node_id") or ev_dict.get("node_id") or ""
                    ),
                    "detail": json.dumps(details, ensure_ascii=False) if details else "",
                    "state": _format_state_display(
                        _get_attr_or_key(ev, "state") or ev_dict.get("state")
                    ),
                }
            )

    return {
        "present": True,
        "status": status,
        "initial_state": _format_state_display(initial_state),
        "final_state": _format_state_display(final_state),
        "error": str(error_msg) if error_msg else "",
        "rows": rows,
    }


def _extract_proof_info(proof_result: Any | None) -> dict[str, Any]:
    if proof_result is None:
        return {"present": False}
    data = _to_dict_safe(proof_result)
    raw_valid = _get_attr_or_key(
        proof_result, "is_valid", "proved", "valid", "verified"
    )
    if raw_valid is None:
        raw_valid = data.get("is_valid", data.get("proved", data.get("valid")))
    status = _get_attr_or_key(proof_result, "status") or data.get("status")
    if status is None:
        status = "proved" if raw_valid else ("disproved" if raw_valid is False else "unknown")

    pre = _get_attr_or_key(proof_result, "precondition") or data.get("precondition") or ""
    post = _get_attr_or_key(proof_result, "postcondition") or data.get("postcondition") or ""
    hyp = (
        _get_attr_or_key(proof_result, "hypothesis", "hypothesis_k", "invariant", "invariants")
        or data.get("hypothesis")
        or data.get("hypothesis_k")
        or data.get("invariants")
        or ""
    )
    hyp_str = _format_state_display(hyp) if isinstance(hyp, dict) else str(hyp)
    explanation = (
        _get_attr_or_key(proof_result, "explanation_text", "explanation", "summary")
        or data.get("explanation_text")
        or data.get("explanation")
        or ""
    )
    counterexample = _get_attr_or_key(proof_result, "counterexample") or data.get("counterexample")
    counterexample_str = _format_state_display(counterexample) if counterexample else ""
    if not counterexample_str:
        cxs = _get_attr_or_key(proof_result, "counterexamples") or data.get("counterexamples") or []
        if cxs:
            cx_parts: list[str] = []
            for cx in cxs[:3]:
                cx_dict = _to_dict_safe(cx)
                init_st = _get_attr_or_key(cx, "initial_state") or cx_dict.get("initial_state")
                reason = _get_attr_or_key(cx, "reason") or cx_dict.get("reason") or str(cx)
                if init_st:
                    cx_parts.append(f"{_format_state_display(init_st)}: {reason}")
                else:
                    cx_parts.append(str(reason))
            counterexample_str = "; ".join(cx_parts)

    raw_vcs = (
        _get_attr_or_key(proof_result, "verification_conditions", "vcs", "steps", "obligations")
        or data.get("verification_conditions")
        or data.get("steps")
        or []
    )
    vcs: list[dict[str, str]] = []
    for idx, vc in enumerate(raw_vcs, start=1):
        vc_dict = _to_dict_safe(vc)
        vcs.append(
            {
                "name": str(
                    _get_attr_or_key(vc, "name", "rule", "label", "title")
                    or vc_dict.get("name")
                    or vc_dict.get("title")
                    or f"VC {idx}"
                ),
                "formula": str(
                    _get_attr_or_key(vc, "formula", "condition", "statement")
                    or vc_dict.get("formula")
                    or ""
                ),
                "status": str(
                    _get_attr_or_key(vc, "status", "valid", "proved")
                    or vc_dict.get("status")
                    or ""
                ),
                "ast_node_id": str(
                    _get_attr_or_key(vc, "ast_node_id", "node_id")
                    or vc_dict.get("ast_node_id")
                    or ""
                ),
            }
        )

    if not vcs:
        for attr_name in (
            "base_case",
            "inductive_step",
            "termination_and_exit",
            "backward_induction",
        ):
            step_obj = _get_attr_or_key(proof_result, attr_name) or data.get(attr_name)
            if step_obj is None:
                continue
            step_dict = _to_dict_safe(step_obj)
            title = str(_get_attr_or_key(step_obj, "title") or step_dict.get("title") or attr_name)
            formula = str(
                _get_attr_or_key(step_obj, "formula", "details")
                or step_dict.get("formula")
                or step_dict.get("details")
                or ""
            )
            st_status = str(_get_attr_or_key(step_obj, "status") or step_dict.get("status") or "")
            vcs.append(
                {
                    "name": title,
                    "formula": formula,
                    "status": st_status,
                    "ast_node_id": "",
                }
            )

    return {
        "present": True,
        "status": str(status),
        "is_ok": str(status).lower() in ("proved", "valid", "ok", "true", "verified"),
        "precondition": str(pre),
        "postcondition": str(post),
        "hypothesis": hyp_str,
        "explanation_text": str(explanation),
        "counterexample": counterexample_str,
        "vcs": vcs,
    }


def render_pipeline_html(
    result: ParseResult,
    *,
    semantic_term: Any | None = None,
    eval_result: Any | None = None,
    proof_result: Any | None = None,
) -> str:
    """Render a self-contained 5-panel synchronized HTML5 report for the full SIPL pipeline."""
    source_html = _build_interactive_source_html(result)
    pt_svg = _strip_xml_decl(render_parse_tree_svg(result))
    ast_svg = _strip_xml_decl(render_ast_svg(result))
    cmp_data = compare_parse_tree_and_ast(result)

    sem_info = _extract_semantic_info(semantic_term)
    eval_info = _extract_eval_info(eval_result)
    proof_info = _extract_proof_info(proof_result)

    crown_cls = "ok" if result.is_crown_valid else "err"
    crown_status = "OK" if result.is_crown_valid else "MISMATCH"

    if sem_info["present"]:
        steps_rows = "".join(
            f'<tr data-ast-id="{_esc_xml(st["ast_node_id"])}">'
            f"<td>{_esc_xml(st['index'])}</td>"
            f"<td><code>{_esc_xml(st['rule'])}</code></td>"
            f"<td><code>{_esc_xml(st['ast_node_id'] or '—')}</code></td>"
            f"<td><code>{_esc_xml(st['fragment'])}</code></td>"
            f"<td><code>{_esc_xml(st['term'])}</code></td>"
            f"<td>{_esc_xml(st['note'])}</td></tr>"
            for st in sem_info["steps"]
        )
        steps_table = (
            '<table class="sipl-table"><thead><tr>'
            "<th>#</th><th>Rule</th><th>AST</th><th>Fragment</th><th>Term</th><th>Notes</th>"
            f"</tr></thead><tbody>{steps_rows}</tbody></table>"
            if steps_rows
            else '<p class="muted">No step-by-step NS derivation entries attached.</p>'
        )
        latex_block = (
            "<div><strong>LaTeX:</strong>"
            f'<pre class="formula">{_esc_xml(sem_info["latex"])}</pre></div>'
            if sem_info["latex"]
            else ""
        )
        sem_body_html = (
            "<div><strong>Unicode:</strong>"
            f'<pre class="formula">{_esc_xml(sem_info["unicode"])}</pre></div>'
            f"{latex_block}"
            f"<div><strong>Derivation Steps (NS):</strong>{steps_table}</div>"
        )
    else:
        sem_body_html = (
            '<p class="muted">Semantic term not provided. Pass <code>semantic_term=...</code> '
            "to render Unicode/LaTeX denotation and step-by-step NS derivation rules.</p>"
        )

    if eval_info["present"]:
        eval_rows = "".join(
            f'<tr data-ast-id="{_esc_xml(row["ast_node_id"])}">'
            f"<td>{_esc_xml(row['step'])}</td>"
            f"<td><code>{_esc_xml(row['rule'])}</code></td>"
            f"<td><code>{_esc_xml(row['ast_node_id'] or '—')}</code></td>"
            f"<td><code>{_esc_xml(row['detail'])}</code></td>"
            f"<td><code>{_esc_xml(row['state'])}</code></td></tr>"
            for row in eval_info["rows"]
        )
        eval_table = (
            '<table class="sipl-table"><thead><tr>'
            "<th>Step</th><th>Rule / Event</th><th>AST</th><th>Details</th><th>State</th>"
            f"</tr></thead><tbody>{eval_rows}</tbody></table>"
            if eval_rows
            else '<p class="muted">No trace steps recorded.</p>'
        )
        err_banner = (
            f'<p class="badge err">Error: {_esc_xml(eval_info["error"])}</p>'
            if eval_info["error"]
            else ""
        )
        eval_html = (
            f'<p><strong>Status:</strong> <code>{_esc_xml(eval_info["status"])}</code> | '
            f'<strong>Initial:</strong> <code>{_esc_xml(eval_info["initial_state"])}</code> &rarr; '
            f'<strong>Final:</strong> <code>{_esc_xml(eval_info["final_state"])}</code></p>'
            f"{err_banner}{eval_table}"
        )
    else:
        eval_html = (
            '<p class="muted">Evaluation trace not provided. Pass <code>eval_result=...</code> '
            "to inspect AF state transitions and runtime trace events.</p>"
        )

    if proof_info["present"]:
        p_cls = "ok" if proof_info["is_ok"] else "err"
        vc_rows = "".join(
            f'<tr data-ast-id="{_esc_xml(vc["ast_node_id"])}">'
            f"<td><code>{_esc_xml(vc['name'])}</code></td>"
            f"<td><code>{_esc_xml(vc['formula'])}</code></td>"
            f"<td>{_esc_xml(vc['status'])}</td></tr>"
            for vc in proof_info["vcs"]
        )
        vc_table = (
            '<table class="sipl-table"><thead><tr>'
            "<th>Condition / Rule</th><th>Formula</th><th>Status</th>"
            f"</tr></thead><tbody>{vc_rows}</tbody></table>"
            if vc_rows
            else ""
        )
        ce_html = (
            "<p><strong>Counterexample:</strong> "
            f'<code>{_esc_xml(proof_info["counterexample"])}</code></p>'
            if proof_info["counterexample"]
            else ""
        )
        exp_html = (
            f'<pre class="formula">{_esc_xml(proof_info["explanation_text"])}</pre>'
            if proof_info["explanation_text"]
            else ""
        )
        proof_html = (
            '<div style="margin-top:12px; padding-top:10px; border-top:1px solid #e2e8f0;">'
            f'<p><strong>Correctness Proof:</strong> <span class="badge {p_cls}">'
            f'{_esc_xml(proof_info["status"])}</span></p>'
            + (
                "<p><strong>Precondition {{P}}:</strong> "
                f'<code>{_esc_xml(proof_info["precondition"])}</code></p>'
                if proof_info["precondition"]
                else ""
            )
            + (
                "<p><strong>Postcondition {{Q}}:</strong> "
                f'<code>{_esc_xml(proof_info["postcondition"])}</code></p>'
                if proof_info["postcondition"]
                else ""
            )
            + (
                "<p><strong>Hypothesis / Invariant:</strong> "
                f'<code>{_esc_xml(proof_info["hypothesis"])}</code></p>'
                if proof_info["hypothesis"]
                else ""
            )
            + ce_html
            + exp_html
            + vc_table
            + "</div>"
        )
    else:
        proof_html = (
            '<div style="margin-top:12px; padding-top:10px; border-top:1px solid #e2e8f0;">'
            '<p class="muted">No correctness proof attached '
            "(pass <code>proof_result=...</code>).</p>"
            "</div>"
        )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1.0"/>
  <title>SIPL Full Pipeline Visualizer</title>
  <style>{_SHARED_HTML_CSS}</style>
</head>
<body>
  <header class="topbar">
    <h1>SIPL Language Toolkit &mdash; Interactive Pipeline Visualizer</h1>
    <div class="badges">
      <span class="badge {crown_cls}">Crown: {crown_status}</span>
      <span class="badge">Leaves: {cmp_data['parse_tree_terminal_count']}</span>
      <span class="badge">PT Nodes: {cmp_data['parse_tree_node_count']}</span>
      <span class="badge">AST Nodes: {cmp_data['ast_node_count']}</span>
    </div>
  </header>

  <div class="selection-bar">
    <span id="sipl-selection-info">
      Click any Source token, Parse Tree node, AST node, or Derivation step to highlight.
    </span>
    <button id="sipl-clear-selection" type="button">Clear (Esc)</button>
  </div>

  <div class="grid-pipeline">
    <section class="panel full" id="panel-source">
      <div class="panel-head">
        <span>1. Source Code</span>
        <span class="muted">Click any token to inspect AST &amp; Parse Tree links</span>
      </div>
      <div class="panel-body">
        <div class="src-code">{source_html}</div>
      </div>
    </section>

    <section class="panel" id="panel-parse-tree">
      <div class="panel-head">
        <span>2. Concrete Parse Tree</span>
        <span class="muted">{cmp_data['parse_tree_node_count']} nodes</span>
      </div>
      <div class="panel-body">
        <div class="svg-wrap">{pt_svg}</div>
      </div>
    </section>

    <section class="panel" id="panel-ast">
      <div class="panel-head">
        <span>3. Typed Abstract Syntax Tree (AST)</span>
        <span class="muted">{cmp_data['ast_node_count']} nodes</span>
      </div>
      <div class="panel-body">
        <div class="svg-wrap">{ast_svg}</div>
      </div>
    </section>

    <section class="panel" id="panel-semantic-term">
      <div class="panel-head">
        <span>4. Semantic Term &amp; NS Derivation</span>
        <span class="muted">Denotational / Functional Semantics</span>
      </div>
      <div class="panel-body">{sem_body_html}</div>
    </section>

    <section class="panel" id="panel-eval-proof">
      <div class="panel-head">
        <span>5. State Transitions (AF) &amp; Correctness Proof</span>
        <span class="muted">Execution Trace &amp; Verification</span>
      </div>
      <div class="panel-body">
        {eval_html}
        {proof_html}
      </div>
    </section>
  </div>

  <script>{_SHARED_HIGHLIGHT_JS}</script>
</body>
</html>"""
