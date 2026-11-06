#!/usr/bin/env python3
"""Check the paper-Lean contract: the numbered results of paper/sections/*.tex against the
entries of DeciENSSE/Paper/*.lean (see scripts/README-contract.md). Python 3, standard
library only."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED = {"complexity.tex", "appendix-complexity.tex", "appendix-lean.tex",
            "mechanization.tex"}
REQUIRED = {"theorem", "lemma", "proposition", "corollary"}
KINDS = REQUIRED | {"definition", "example"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class ContractError(ValueError):
    pass


@dataclass(frozen=True)
class Result:
    label: str
    kind: str
    section: str
    items: int

    @property
    def keys(self):
        return [(self.label, i) for i in range(1, self.items + 1)] if self.items else [(self.label, None)]


@dataclass(frozen=True)
class Entry:
    label: str
    item: int | None
    kind: str
    name: str
    note: str
    source: str
    decl: str = "theorem"

    @property
    def key(self):
        return self.label, self.item

    @property
    def computable(self):
        return self.decl in DEFINITIONS


def display(key):
    label, item = key
    return label + (f"({item})" if item is not None else "")


def uncomment_tex(text):
    # Consume escaped characters first: \% is literal, but \\% starts a comment.
    return re.sub(r"\\.|%[^\n]*", lambda m: "" if m[0].startswith("%") else m[0], text)


def collect_paper(root=ROOT):
    results = {}
    token = re.compile(r"\\(begin|end|label)\s*\{([^{}]+)\}|\\item\b")
    for path in sorted((root / "paper/sections").glob("*.tex")):
        if path.name in EXCLUDED:
            continue
        stack = []
        active = None
        for match in token.finditer(uncomment_tex(path.read_text(encoding="utf-8"))):
            command, value = match.groups()
            if command == "begin":
                if value in KINDS:
                    if active is not None:
                        raise ContractError(f"{path}: nested numbered result")
                    active = {"kind": value, "depth": len(stack), "labels": [], "items": 0}
                stack.append(value)
            elif command == "end":
                if not stack or stack[-1] != value:
                    raise ContractError(f"{path}: unbalanced environment {value}")
                stack.pop()
                if active is not None and len(stack) == active["depth"]:
                    labels = active["labels"]
                    if not labels and value not in REQUIRED:
                        active = None
                        continue
                    if not labels:
                        raise ContractError(f"{path}: {value} needs a result label")
                    for label in labels:
                        if label in results:
                            raise ContractError(f"duplicate paper label: {label}")
                        results[label] = Result(label, value, path.name, active["items"])
                    active = None
            elif command == "label" and active is not None:
                if len(stack) == active["depth"] + 1:
                    active["labels"].append(value)
            elif command is None and active is not None:
                nested = stack[active["depth"] + 1:]
                if nested == ["enumerate"]:
                    active["items"] += 1
        if stack or active is not None:
            raise ContractError(f"{path}: unclosed environment")
    return results


def lean_code_and_docs(text):
    """Mask strings and nested comments, retaining offsets and documentation."""
    code = list(text)
    docs = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                i = len(text)
        elif text.startswith("/-", i):
            doc = text.startswith("/--", i)
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ContractError("unterminated Lean comment")
            if doc:
                docs.append((start, i, text[start + 3:i - 2].strip()))
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if code[j] != "\n":
                code[j] = " "
    return "".join(code), docs


HEADER = re.compile(r"\*\*(Theorem|Lemma|Proposition|Corollary|Definition|Example) \((.+)\)\*\*, `([^`]+)`(?:\(([1-9][0-9]*)\))?\.")
COMMAND = re.compile(
    r"(?m)^[ \t]*(?:(?:(noncomputable)[ \t]+)?(namespace|section|end)\b[ \t]*([\w.']*)|"
    r"((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(theorem|lemma|abbrev|def|axiom|opaque)\s+([\w.']+))")
DECLARATIONS = {"theorem", "lemma", "def", "abbrev"}
DEFINITIONS = {"def", "abbrev"}
# Classical logic proves `Nonempty (Decidable P)` for every `P`: such a statement is vacuous.
VACUOUS_DECIDABLE = re.compile(r"\bNonempty\b(?:\s|\(|<\||\$)*Decidable(?:Pred|Rel|Eq)?\b")


def statement_of(code, start, stop):
    """Return the masked declaration header: everything before the first top-level `:=`."""
    depth = 0
    for i in range(start, stop):
        ch = code[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth = max(depth - 1, 0)
        elif depth == 0 and code.startswith(":=", i):
            return code[start:i]
    return code[start:stop]


def collect_entries(root=ROOT):
    entries = []
    for path in sorted((root / "DeciENSSE/Paper").glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        code, docs = lean_code_and_docs(text)
        scopes = []
        attached = set()
        matches = list(COMMAND.finditer(code))
        for index, match in enumerate(matches):
            nc_scope, scope, name, modifiers, kind, name_decl = match.groups()
            line = text.count("\n", 0, match.start()) + 1
            source = f"{path.relative_to(root)}:{line}"
            if scope:
                if nc_scope and scope != "section":
                    raise ContractError(f"{source}: noncomputable {scope}")
                if scope == "end":
                    if not scopes:
                        raise ContractError(f"{path}: unmatched end")
                    scopes.pop()
                else:
                    scopes.append((scope, name, bool(nc_scope)))
                continue
            candidates = [(j, doc) for j, doc in enumerate(docs) if doc[1] <= match.start()]
            if not candidates:
                raise ContractError(f"{source}: declaration has no contract docstring")
            j, (_, end, doc) = candidates[-1]
            between = re.sub(r"@\[[^\]]*\]", "", code[end:match.start()])
            if between.strip() or j in attached:
                raise ContractError(f"{source}: declaration has no attached contract docstring")
            attached.add(j)
            header = HEADER.fullmatch(doc.splitlines()[0])
            if not header:
                raise ContractError(f"{source}: invalid first docstring line")
            doc_kind, _, label, item = header.groups()
            if kind not in DECLARATIONS or "private" in modifiers:
                raise ContractError(f"{source}: entries must be public theorems or definitions")
            if "noncomputable" in modifiers.split() or any(nc for _, _, nc in scopes):
                raise ContractError(f"{source}: entries must be computable; {name_decl} is noncomputable")
            if {"unsafe", "partial"} & set(modifiers.split()):
                raise ContractError(f"{source}: entries must be safe total declarations")
            stop = min([m.start() for m in matches[index + 1:index + 2]]
                       + [d[0] for d in docs if d[0] > match.start()] + [len(code)])
            vacuous = VACUOUS_DECIDABLE.search(statement_of(code, match.end(), stop))
            if vacuous:
                raise ContractError(f"{source}: the statement contains `{vacuous[0]}`, which holds "
                                    "classically for every proposition; state decidability as a "
                                    "computable definition")
            full_name = ".".join([s for k, s, _ in scopes if k == "namespace"] + [name_decl])
            expected = "DeciENSSE.Paper." + re.sub(r"[^A-Za-z0-9_]", "_", label)
            if item:
                expected += "_" + item
            if full_name != expected:
                raise ContractError(f"{source}: expected declaration {expected}, found {full_name}")
            notes = [line.strip()[6:] for line in doc.splitlines()[1:] if line.strip().startswith("Form: ")]
            if len(notes) > 1:
                raise ContractError(f"{source}: multiple Form lines")
            entries.append(Entry(label, int(item) if item else None, doc_kind.lower(),
                                 full_name, notes[0] if notes else "", source, kind))
        for j, (_, _, doc) in enumerate(docs):
            if j not in attached:
                raise ContractError(f"{path}: unattached contract docstring: {doc.splitlines()[0]}")
    return entries


def check(results, entries):
    present = {e.key for e in entries}
    missing = defaultdict(list)
    for result in results.values():
        if result.kind in REQUIRED and not result.label.startswith("rem:"):
            missing[result.section].extend(key for key in result.keys if key not in present)
    missing = {section: keys for section, keys in missing.items() if keys}
    dangling = [e for e in entries if e.label not in results or e.key not in results[e.label].keys
                or e.kind != results[e.label].kind]
    duplicates = [key for key, count in Counter(e.key for e in entries).items() if count > 1]
    print(f"Paper: {len(results)} result labels; "
          f"{sum(len(r.keys) for r in results.values() if r.kind in REQUIRED and not r.label.startswith('rem:'))} required entries.")
    print(f"Lean: {len(entries)} entries.")
    print(f"Missing required entries: {sum(map(len, missing.values()))}")
    for section, keys in missing.items():
        print(f"  {section}: " + ", ".join(map(display, keys)))
    print(f"Dangling/invalid entries: {len(dangling)}")
    for e in dangling:
        print(f"  {display(e.key)}: {e.name} ({e.source})")
    print(f"Duplicate entries: {len(duplicates)}")
    for key in duplicates:
        print(f"  {display(key)}: " + ", ".join(e.source for e in entries if e.key == key))
    return missing, dangling, duplicates


def check_axioms(entries, root=ROOT):
    modules = [".".join(p.relative_to(root).with_suffix("").parts)
               for p in sorted((root / "DeciENSSE/Paper").glob("*.lean"))]
    contents = "\n".join(f"import {m}" for m in modules) + "\n"
    contents += "\n".join(f"#print axioms {e.name}" for e in entries) + "\n"
    # Compile check without evaluation: a computable definition that refers to an entry fails
    # to compile when the entry has no executable code (Classical.choice, noncomputable).
    definitions = [e for e in entries if e.computable]
    contents += "namespace ContractProbe\n" + "".join(
        f"def compile_{i} := @{e.name}\n" for i, e in enumerate(definitions)) + "end ContractProbe\n"
    lock = os.environ.get("LAKE_LOCK")
    command = ["zsh", lock] if lock else ["lake"]
    # Keep the probe outside the source tree and remove it even on failure.
    with tempfile.TemporaryDirectory(prefix="paper-contract-") as tmp:
        probe = Path(tmp) / "Axioms.lean"
        probe.write_text(contents, encoding="utf-8")
        print("Checking axioms and compiling definitions via " + " ".join(command)
              + " env lean <temporary file>", flush=True)
        process = subprocess.run(command + ["env", "lean", str(probe)], cwd=root,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if process.returncode:
        raise ContractError(f"Lean axiom/compilation probe failed ({process.returncode}):\n{process.stdout}")
    observed = defaultdict(list)
    pattern = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    for match in pattern.finditer(process.stdout):
        observed[match[1]].append(set(re.findall(r"[\w.]+", match[2] or "")))
    for entry in entries:
        reports = observed[entry.name]
        if len(reports) != 1:
            raise ContractError(f"expected one axiom report for {entry.name}, got {len(reports)}:\n{process.stdout}")
        unexpected = reports[0] - ALLOWED_AXIOMS
        if unexpected:
            raise ContractError(f"{entry.name}: forbidden axioms: {', '.join(sorted(unexpected))}")
    print(f"Axioms: {len(entries)} entries passed (only propext, Classical.choice, Quot.sound).")
    print(f"Compilation: {len(definitions)} definition entries compiled to executable code.")


def tex_escape(text):
    escapes = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
               "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
               "^": r"\textasciicircum{}"}
    return "".join(escapes.get(c, c) for c in text)


def write_table(path, results, entries):
    order = {key: i for i, key in enumerate(key for r in results.values() for key in r.keys)}
    lines = ["% Generated by scripts/contract.py; longtable body only."]
    for e in sorted(entries, key=lambda e: order[e.key]):
        item = f"({e.item})" if e.item is not None else ""
        lines.append(r"\cref{" + e.label + "}" + item + r" & \lean{" + e.name + "} & "
                     + tex_escape(e.note) + r" \\")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Table: {len(entries)} rows written to {path}.")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true", help="also fail on missing required entries")
    parser.add_argument("--axioms", action="store_true", help="check the axioms and the executable code of the entries in the built library; runs Lean through zsh $LAKE_LOCK when set")
    parser.add_argument("--table", type=Path, metavar="OUT.TEX", help="write the rows of the correspondence table")
    args = parser.parse_args(argv)
    try:
        results = collect_paper()
        entries = collect_entries()
        missing, dangling, duplicates = check(results, entries)
        if dangling or duplicates:
            return 1
        if args.axioms:
            check_axioms(entries)
        if args.table:
            write_table(args.table, results, entries)
        return int(args.strict and bool(missing))
    except (ContractError, OSError) as error:
        print(f"Contract error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
