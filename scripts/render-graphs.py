#!/usr/bin/env python3
"""Render the dependency graphs under docs/ to SVG and PNG.

The .dot files are sources, not finished graphs. A node lists its port status
and a few text fields instead of an HTML label:

    "isZero" [status=gate, gate="Model/eDSL.lean", old="Lang.lean:10", aptos="IsZero"];

This script expands each such node into its table label, colors the header by
status, counts the legend, and fades every edge into a cluster that sets
`fade=true`. To record progress on a gadget, change its `status` and rerun.

The statuses and their colors are in STATUSES below. The fields are, in display
order: `new` or `gate`, `file`, `old`, `aptos`, and `note` (repeatable). A
missing `new` or `old` shows as "—". The `legend` node takes only `note`s,
printed under the counts. Nodes without these fields are passed through as is.

    scripts/render-graphs.py [FILE...]        # write FILE's .svg and .png (default: GRAPHS)
    scripts/render-graphs.py --emit-dot FILE  # print FILE expanded; render nothing

Run it from the repository root, with Graphviz's `dot` on the PATH.
"""

import html
import re
import subprocess
import sys
from collections import Counter

GRAPHS = [
    "docs/keyless-dependency-graph.dot",
    "docs/aptos-circom-dependency-graph.dot",
]

# status: (header color, legend text). The legend lists them in this order.
STATUSES = {
    "proven": ("#a8dba8", "proven (convertsM, no sorry)"),
    "sorry": ("#ffb870", "ported, spec has sorry"),
    "nospec": ("#fff1a0", "ported, no spec"),
    "todo": ("#f4a6a6", "not ported"),
    "gate": ("#b4d4f0", "CLAP gate (eDSL primitive)"),
}
FIELDS = ["status", "new", "gate", "file", "old", "aptos", "note"]
REPEATABLE = {"note"}
FADED_EDGE = "#00000030"
APTOS_COLOR = "#555555"
LEGEND = "legend"

ID = r'"[^"]+"|[\w.]+'
NODE = re.compile(rf"^(\s*)({ID})\s*\[(.*)\];\s*$", re.S)
NODE_START = re.compile(rf"^\s*({ID})\s*\[")
EDGE = re.compile(rf"^(\s*)({ID})\s*->\s*({ID})\s*;\s*$")
ATTR = re.compile(r'(\w+)\s*=\s*("(?:[^"\\]|\\.)*"|[^,;\s\]]+)\s*[,;]?')
SUBGRAPH = re.compile(r"^\s*subgraph\s+(\S+)\s*\{")
FADE = re.compile(r'(?:^|[;\s])fade\s*=\s*"?true\b')
KEYWORDS = {"graph", "node", "edge", "subgraph"}


class GraphError(Exception):
    pass


def unquote(name: str) -> str:
    return name[1:-1] if name.startswith('"') else name


def statements(lines: list[str]):
    """Yield (line number, text), joining a node's attribute list across lines."""
    i = 0
    while i < len(lines):
        start, text = i, lines[i]
        m = NODE_START.match(text)
        if m and unquote(m.group(1)) not in KEYWORDS:
            while not text.rstrip().endswith("];") and i + 1 < len(lines):
                i += 1
                text += lines[i]
        yield start + 1, text
        i += 1


def parse_fields(body: str) -> dict[str, list[str]] | None:
    """The node's attributes, or None if they are not plain key=value pairs."""
    if ATTR.sub("", body).strip():
        return None
    fields: dict[str, list[str]] = {}
    for key, value in ATTR.findall(body):
        if value.startswith('"'):
            value = value[1:-1].replace('\\"', '"')
        fields.setdefault(key, []).append(value)
    return fields


def esc(text: str) -> str:
    return html.escape(text, quote=False)


def row(text: str, size: int, color: str | None = None, italic: bool = False) -> str:
    font = f'<FONT POINT-SIZE="{size}"' + (f' COLOR="{color}"' if color else "") + ">"
    body = f"<I>{esc(text)}</I>" if italic else esc(text)
    return f'<TR><TD ALIGN="LEFT" BALIGN="LEFT">{font}{body}</FONT></TD></TR>'


def node_label(name: str, fields: dict[str, list[str]]) -> str:
    one = {key: values[-1] for key, values in fields.items()}
    rows = [f'<TR><TD BGCOLOR="{STATUSES[one["status"]][0]}"><B>{esc(name)}</B></TD></TR>']
    if "gate" in one:
        rows.append(row(f"gate: {one['gate']}", 9))
    else:
        rows.append(row(f"new: {one.get('new', '—')}", 9))
    if "file" in one:
        rows.append(row(f"     {one['file']}", 8))
    rows.append(row(f"old: {one.get('old', '—')}", 9))
    if "aptos" in one:
        rows.append(row(f"Aptos: {one['aptos']}", 8, APTOS_COLOR, italic=True))
    rows += [row(note, 8, italic=True) for note in fields.get("note", [])]
    table = '<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="3">'
    return f"<{table}{''.join(rows)}</TABLE>>"


def legend_label(counts: Counter, notes: list[str]) -> str:
    rows = ['<TR><TD COLSPAN="3"><B>Legend</B></TD></TR>']
    for status, (color, text) in STATUSES.items():
        if counts[status]:
            rows.append(
                f'<TR><TD BGCOLOR="{color}" WIDTH="24"> </TD><TD ALIGN="LEFT">{esc(text)}</TD>'
                f'<TD ALIGN="RIGHT">{counts[status]}</TD></TR>'
            )
    rows.append(
        '<TR><TD></TD><TD ALIGN="LEFT"><B>total</B></TD>'
        f'<TD ALIGN="RIGHT"><B>{sum(counts.values())}</B></TD></TR>'
    )
    rows += [
        f'<TR><TD COLSPAN="3" ALIGN="LEFT"><FONT POINT-SIZE="9">{esc(note)}</FONT></TD></TR>'
        for note in notes
    ]
    table = '<TABLE BORDER="1" CELLBORDER="0" CELLSPACING="2" CELLPADDING="4" BGCOLOR="white">'
    return f"<{table}{''.join(rows)}</TABLE>>"


def expand(path: str) -> str:
    with open(path, encoding="utf-8") as f:
        stmts = list(statements(f.read().splitlines(keepends=True)))

    # First pass: which cluster each node is in, which clusters fade, and each
    # status node's fields.
    cluster_of: dict[str, str | None] = {}
    faded: set[str] = set()
    nodes: dict[int, dict[str, list[str]]] = {}
    counts: Counter = Counter()
    stack: list[str] = []
    for lineno, text in stmts:
        where = f"{path}:{lineno}"
        if m := SUBGRAPH.match(text):
            stack.append(m.group(1))
        elif text.strip() == "}":
            if stack:
                stack.pop()
        elif (m := NODE.match(text)) and unquote(m.group(2)) not in KEYWORDS:
            name = unquote(m.group(2))
            cluster_of[name] = stack[-1] if stack else None
            fields = parse_fields(m.group(3))
            if fields is None:
                # e.g. a hand-written HTML label, which is passed through
                if re.search(r"\bstatus\s*=", m.group(3)):
                    raise GraphError(f"{where}: node {name}: cannot parse attributes")
                continue
            if name == LEGEND and "status" not in fields:
                if set(fields) - {"note"}:
                    raise GraphError(f"{where}: the legend takes only note=")
                nodes[lineno] = fields
            elif set(fields) & set(FIELDS):
                if unknown := set(fields) - set(FIELDS):
                    raise GraphError(f"{where}: node {name}: unknown field(s) {', '.join(sorted(unknown))}")
                if repeated := [k for k, v in fields.items() if len(v) > 1 and k not in REPEATABLE]:
                    raise GraphError(f"{where}: node {name}: {', '.join(repeated)} given twice")
                status = fields.get("status", [None])[-1]
                if status not in STATUSES:
                    problem = f"unknown status {status!r}" if status else "no status"
                    raise GraphError(
                        f"{where}: node {name}: {problem} (expected one of {', '.join(STATUSES)})"
                    )
                nodes[lineno] = fields
                counts[status] += 1
        elif stack and FADE.search(text):
            faded.add(stack[-1])

    # Second pass: emit, replacing the nodes found above and fading edges.
    out = []
    for lineno, text in stmts:
        if lineno in nodes:
            m = NODE.match(text)
            indent, raw, name = m.group(1), m.group(2), unquote(m.group(2))
            if name == LEGEND and "status" not in nodes[lineno]:
                label = legend_label(counts, nodes[lineno].get("note", []))
            else:
                label = node_label(name, nodes[lineno])
            out.append(f"{indent}{raw} [label={label}];\n")
        elif (m := EDGE.match(text)) and cluster_of.get(unquote(m.group(3))) in faded:
            indent, src, dst = m.groups()
            out.append(f'{indent}{src} -> {dst} [color="{FADED_EDGE}"];\n')
        else:
            out.append(text)
    return "".join(out)


def render(path: str) -> None:
    dot = expand(path)
    base = path[: -len(".dot")]
    for fmt in ("svg", "png"):
        subprocess.run(["dot", f"-T{fmt}", "-o", f"{base}.{fmt}"], input=dot, text=True, check=True)
    print(f"wrote {base}.svg, {base}.png")


def main(argv: list[str]) -> int:
    try:
        if argv[:1] == ["--emit-dot"]:
            if len(argv) != 2:
                print("usage: scripts/render-graphs.py --emit-dot FILE", file=sys.stderr)
                return 2
            sys.stdout.write(expand(argv[1]))
            return 0
        for path in argv or GRAPHS:
            render(path)
    except GraphError as e:
        print(e, file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as e:
        print(f"dot failed with exit status {e.returncode}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
