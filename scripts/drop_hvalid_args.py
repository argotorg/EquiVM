#!/usr/bin/env python3
"""Remove the argument for a dropped `hvalid` hypothesis at every call of a block theorem.

Usage: drop_hvalid_args.py <dir> <blocks namespace> [<stem>] [--apply] [--show] [--bare]

When block summaries are regenerated from a listing (`scaffold.py blocks`, `Bytecode.lean` a listing),
a block that jumps to a literal target loses its `hvalid` hypothesis.  This compares the block
files `<dir>/<stem>_NNN.lean` or `<dir>/<stem>.lean` (stem `RuntimeBlocks` by default) at HEAD with the working tree to
find those theorems and the position `hvalid` had among their explicit hypotheses, then removes
that argument at every use `<blocks namespace>.<theorem> …` in the other `.lean` files of
`<dir>`.  Without `--apply` nothing is written; `--show` prints each argument it would remove.
Calls it cannot parse are listed; fix those by hand.  The stem may name a subdirectory
(`Blocks/Runtime` for `<dir>/Blocks/Runtime_NNN.lean`).  With `--bare`, files that `open` the
namespace also have their unqualified uses `<theorem> …` handled.
"""
import re, subprocess, sys, pathlib
directory = pathlib.Path(sys.argv[1]); ns = sys.argv[2]; apply = "--apply" in sys.argv
show = "--show" in sys.argv; bare = "--bare" in sys.argv
stem = sys.argv[3] if len(sys.argv) > 3 and not sys.argv[3].startswith("--") else "RuntimeBlocks"

def hyps(text):
    out = {}
    for m in re.finditer(r"(?m)^theorem (\S+) [^\n]*\n((?:    \([^\n]*\n)*)", text):
        out[m.group(1)] = re.findall(r"(?m)^    \((\w+) :", m.group(2))
    return out

dropped = {}
# `<stem>.lean` too: an unsharded block file (Safe's `Blocks/Creation.lean`)
for path in sorted([*directory.glob(stem + "_*.lean"), *directory.glob(stem + ".lean")]):
    old = hyps(subprocess.run(["git", "show", f"HEAD:{path}"], capture_output=True, text=True).stdout)
    new = hyps(path.read_text())
    for name, hs in old.items():
        if "hvalid" in hs and "hvalid" not in new.get(name, ["hvalid"]):
            dropped[name] = hs.index("hvalid")
print(f"{len(dropped)} theorems lost hvalid", file=sys.stderr)

IDENT = re.compile(r"[A-Za-z_\u03b1-\u03c9\u2080-\u2089][\w.'!?\u03b1-\u03c9\u2080-\u2089✝]*")
STOP_WORDS = {"at", "with", "using", "from", "then", "else", "by", "fun", "in", "do", "have", "exact",
              "obtain", "refine", "rw", "simp", "simpa", "dsimp", "show", "calc", "intro", "apply"}
PAIRS = {"(": ")", "⟨": "⟩", "[": "]", "{": "}"}

def balanced(src, i):
    stack = [PAIRS[src[i]]]; i += 1
    while stack:
        c = src[i]
        if c in PAIRS: stack.append(PAIRS[c])
        elif c == stack[-1]: stack.pop()
        i += 1
    return i

def line_indent(src, i):
    start = src.rfind("\n", 0, i) + 1
    return len(src[start:i]) - len(src[start:i].lstrip(" ")) if src[start:i].strip() == "" else None

def args_after(src, i):
    """Explicit argument spans after position i (end of the theorem name)."""
    start = src.rfind("\n", 0, i) + 1
    line = src[start:src.find("\n", i)]
    base = len(line) - len(line.lstrip(" "))
    if line.lstrip().startswith(ns + ".") or (bare and line.lstrip().startswith(src[start:i].split()[-1])):
        base -= 1
    out = []
    while True:
        j = i
        while j < len(src) and src[j] in " \n":
            j += 1
        if j >= len(src): break
        if "\n" in src[i:j]:
            ind = j - (src.rfind("\n", 0, j) + 1)
            if ind <= base: break
        c = src[j]
        if c in PAIRS:
            k = balanced(src, j)
            if c == "{": break
            named = re.match(r"\(\s*[\w']+\s*:=", src[j:k]) is not None
            if not named: out.append((j, k))
            i = k; continue
        if src.startswith("?_", j): out.append((j, j + 2)); i = j + 2; continue
        m = IDENT.match(src, j)
        if m and m.group(0) not in STOP_WORDS:
            out.append((j, m.end())); i = m.end(); continue
        break
    return out

problems = []; edits = 0
files = [p for p in sorted(directory.glob("*.lean"))
         if not re.search(r"Blocks_\d+\.lean$|^(?:Creation)?(?:Listing|Bytecode)\.lean$", p.name)]
for path in files:
    src = path.read_text(); cuts = []
    pattern = re.escape(ns) + r"\.(\w+)"
    if bare and re.search(r"(?m)^open .*(?<![\w.])" + re.escape(ns) + r"(?![\w.])", src):
        pattern += r"|(?<![\w.'])(\w+)"
    for m in re.finditer(pattern, src):
        name = m.group(1) or m.group(2)
        if name not in dropped: continue
        lineno = src.count("\n", 0, m.start()) + 1
        # only applications: skip mentions inside simp/dsimp lists and doc text
        args = args_after(src, m.end())
        idx = dropped[name]
        if idx >= len(args):
            before = src[max(0, m.start() - 1)]
            problems.append(f"{path.name}:{lineno}: {name}: {len(args)} explicit args, need index {idx}")
            continue
        cuts.append(args[idx])
        if show: print("CUT", re.sub(r"\d+", "N", src[args[idx][0]:args[idx][1]])[:90])
    for a, b in sorted(cuts, reverse=True):
        line_start = src.rfind("\n", 0, a) + 1
        line_end = src.find("\n", b)
        if src[line_start:a].strip() == "" and src[b:line_end].strip() == "":
            src = src[:line_start - 1] + src[line_end:]          # alone on its line: drop the line
        elif src[line_start:a].strip() == "":
            c = b
            while src[c] == " ": c += 1
            src = src[:a] + src[c:]                              # first on its line: keep the indent
        else:
            c = a
            while src[c - 1] == " ": c -= 1
            src = src[:c] + src[b:]                              # drop it and the space before
        edits += 1
    if apply and cuts: path.write_text(src)
print(f"{edits} arguments removed in {len(files)} files; {len(problems)} calls not handled", file=sys.stderr)
for p in problems[:40]: print(p)
