"""Dependency graph of the .v files of the repository, as DOT.

Usage: python3 tools/depgraph.py DEPS REPO > doc/deps.dot (`make depgraph`)
  DEPS: the output of `rocq dep -f _CoqProject <the .v files>`, or - for
        the standard input
  REPO: the repository root (to find the imports of Undecidability)

An edge A -> B: B requires A (A comes first). The files are grouped by
directory, in nested clusters; the modules of coq-library-undecidability
that are imported are a cluster of their own (`rocq dep` omits the
installed libraries: they are found from the `From Undecidability...
Require` lines). Stdlib and Ltac2 are left out.
"""
import os
import re
import sys
from collections import defaultdict

deps_file, repo = sys.argv[1], sys.argv[2]
deps_lines = sys.stdin if deps_file == "-" else open(deps_file)

# The order of the directories among their siblings: roughly from the
# foundations to the applications.
ORDER = ["math", "compiler", "models", "core", "time", "counting", "space",
         "stdlib", "instances", "machine", "examples", "lower", "bff"]
# The links of the nodes (in the SVG), relative to doc/ where the graph is
# drawn: the pages of the documentation of the files (`make doc`, html/,
# named after the logical paths: html/Complexity.models.time.TimeLists.html),
# its table of contents for the directories, and the repository of
# coq-library-undecidability.
HTML_DIR = "../html/"
LOGICAL_ROOT = "Complexity"   # -R theories Complexity (_CoqProject)
UNDEC_URL = "https://github.com/uds-psl/coq-library-undecidability"

def doc_url(f):
    """models/time/TimeLists -> ../html/Complexity.models.time.TimeLists.html"""
    return f'{HTML_DIR}{LOGICAL_ROOT}.{f.replace("/", ".")}.html'

# The fill colours of the directories; the others (models/) are outlined.
COLORS = {
    "math": "#e8f0fe", "compiler": "#fef3e2",
    "lower": "#eeeeee", "bff": "#e3ecf7",
    "models/core": "#fde8e8",
    "models/time": "#e6f4ea", "models/time/stdlib": "#fff8d6",
    "models/time/machine": "#d8f0f0", "models/time/machine/examples": "#eaf8f8",
    "models/time/instances": "#fde8f4",
    "models/time/examples": "#f4f7ec", "models/time/examples/eth": "#e7eed8",
    "models/counting": "#fdeedd", "models/counting/examples": "#fff6ec",
    "models/space": "#f3e8fd", "models/space/examples": "#faf4ff",
}

def node(path):
    """theories/models/time/TimeLists.v -> models/time/TimeLists"""
    return re.sub(r"^theories/|\.vo?$", "", path)

edges = set()
files = set()
for line in deps_lines:
    head, _, tail = line.partition(":")
    target = head.split()[0]
    if not target.endswith(".vo"):
        continue  # the .vos lines repeat the .vo ones
    src = node(target)
    files.add(src)
    for d in tail.split():
        if d.startswith("theories/") and d.endswith(".vo"):
            edges.add((node(d), src))

# coq-library-undecidability: the From Undecidability.X Require lines.
undec = set()
req = re.compile(r"^\s*From\s+(Undecidability(?:\.\w+)*)\s+Require\s+(?:Import\s+|Export\s+)?([\w.\s]+?)\.\s*$")
for f in sorted(files):
    for line in open(os.path.join(repo, "theories", f + ".v")):
        m = req.match(line)
        if m:
            for mod in m.group(2).split():
                lib = f"{m.group(1)}.{mod}"
                undec.add(lib)
                edges.add((lib, f))

# The directories, nested: one cluster each, inside that of its parent.
children = defaultdict(set)   # directory -> subdirectories
by_dir = defaultdict(list)    # directory -> files
for f in files:
    d = os.path.dirname(f)
    by_dir[d].append(f)
    while d:
        parent = os.path.dirname(d)
        children[parent].add(d)
        d = parent

def order(d):
    name = os.path.basename(d)
    return (ORDER.index(name) if name in ORDER else len(ORDER), name)

out = ['digraph deps {',
       '  // A -> B: B requires A.',
       '  rankdir=TB; newrank=true; compound=true;',
       '  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10];',
       '  edge [color="#00000060", arrowsize=0.6];']
out.append('  subgraph cluster_undecidability {')
out.append('    label="coq-library-undecidability"; style="dashed"; color="#888888"; fontname="Helvetica";')
out.append(f'    URL="{UNDEC_URL}"; tooltip="{UNDEC_URL}";')
for lib in sorted(undec):
    out.append(f'    "{lib}" [fillcolor="#dddddd", shape=component, URL="{UNDEC_URL}", tooltip="{lib}"];')
out.append('  }')

def emit(d, depth):
    ind = '  ' * depth
    out.append(f'{ind}subgraph cluster_{re.sub(r"[^A-Za-z0-9]", "_", d)} {{')
    color = COLORS.get(d)
    style = f'style="filled"; color="{color}"' if color else 'style="dashed"; color="#888888"'
    out.append(f'{ind}  label="{os.path.basename(d)}/"; {style}; fontname="Helvetica-Bold";')
    out.append(f'{ind}  URL="{HTML_DIR}index.html"; tooltip="theories/{d}/";')
    for f in sorted(by_dir[d]):
        name = f'{LOGICAL_ROOT}.{f.replace("/", ".")}'
        out.append(f'{ind}  "{f}" [label="{os.path.basename(f)}", fillcolor="white", '
                   f'URL="{doc_url(f)}", tooltip="{name} (theories/{f}.v)"];')
    for c in sorted(children[d], key=order):
        emit(c, depth + 1)
    out.append(f'{ind}}}')

for d in sorted(children[""], key=order):
    emit(d, 1)

def cluster(n):
    return "undecidability" if n in undec else os.path.dirname(n)

# The edges between clusters span two ranks: more space between the
# clusters, the files within one stay close. The edges from
# coq-library-undecidability are dashed: a long edge may cross the box of
# an unrelated file, and must not be read as one of its imports.
for a, b in sorted(edges):
    attrs = []
    if cluster(a) != cluster(b):
        attrs.append("minlen=2")
    if a in undec:
        attrs.append('style=dashed, color="#7a5fc0", penwidth=1.3')
    out.append(f'  "{a}" -> "{b}"' + (f' [{", ".join(attrs)}]' if attrs else '') + ';')
out.append('}')
print("\n".join(out))
