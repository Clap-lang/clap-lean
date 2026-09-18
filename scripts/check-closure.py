#!/usr/bin/env python3
"""Report the transitive import closure of the live Lake targets.

Lean modules that are on disk but in no target are never compiled, so nothing
stops them from rotting. This script makes that set explicit: it prints the
closure of each target and then everything under `Clap/` and `R1Serialize/` that
is outside all of them.

Imports inside `/- ... -/` blocks and after `--` are ignored, which matters
because dead import lists have historically been parked in comments.

Exit status is 1 if any live-tree module is unreachable, so this can be wired
into CI.
"""

import os
import re
import sys

ROOTS = ["Clap", "R1Serialize"]
TARGETS = ["Clap", "R1Serialize.R1CS"]
REFERENCE_TREE = "old"


def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return re.sub(r"--.*", "", "".join(out))


def collect() -> dict[str, str]:
    modules = {}
    for root in ROOTS:
        # A library's root module is a sibling of its directory, e.g. Clap.lean.
        if os.path.isfile(f"{root}.lean"):
            modules[root] = f"{root}.lean"
        for dirpath, _, filenames in os.walk(root):
            for name in filenames:
                if name.endswith(".lean"):
                    path = os.path.join(dirpath, name)
                    modules[path[: -len(".lean")].replace(os.sep, ".")] = path
    return modules


def main() -> int:
    modules = collect()
    imports = {
        module: [
            i
            for i in re.findall(
                r"^\s*import\s+([\w.]+)",
                strip_comments(open(path, encoding="utf-8").read()),
                re.M,
            )
            if i in modules
        ]
        for module, path in modules.items()
    }

    reachable = set()
    for target in TARGETS:
        seen, stack = set(), [target]
        while stack:
            module = stack.pop()
            if module in seen:
                continue
            seen.add(module)
            stack.extend(imports.get(module, []))
        print(f"{target}: {len(seen)} modules")
        reachable |= seen

    orphans = sorted(set(modules) - reachable)
    if orphans:
        print(f"\nUnreachable from every target ({len(orphans)}):")
        for module in orphans:
            print(f"  {modules[module]}")
        print(f"\nDead code belongs in {REFERENCE_TREE}/, not in the live tree.")
        return 1

    print("\nEvery module in the live tree is reachable from a target.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
