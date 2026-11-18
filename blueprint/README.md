# Lean proof dependency graph

[Open the interactive graph](https://milind-prabhu.github.io/approximation-preserving-coresets/).
The self-contained `generated/APC_Blueprint.html` also works offline.

The graph contains 492 source declarations, including all 367 audited theorems.
Hover over a node for a short summary. Click it to inspect the checked Lean
statement, source proof, prerequisites, and dependents. Search, proof-specific
views, keyboard navigation, pan, zoom, and fit follow the online carpooling graph.

Arrows point from prerequisite to result. Dependencies come from references in
compiled Lean types and bodies, including paths through generated helper
constants. Each displayed arrow has a compiled-reference witness in
`generated/graph_data.json`. Transitive arrows are removed for readability.
Overview views may omit intermediate declarations. A dependency arrow is not
itself a mathematical hypothesis; read the theorem statement for assumptions.

The overview is also available as SVG, PDF, and PNG in `generated/`.
The earlier [file-import graph](../dependency-graph/README.md) is retained separately.

To regenerate after building the project, install Python 3 and Graphviz and run:

```bash
python3 blueprint/index_sources.py
lake env lean blueprint/Extract.lean
python3 blueprint/build_graph.py
python3 blueprint/check_graph.py
```

`descriptions.json` supplies explanatory hover text; Lean statements and proof
sources are extracted from the project. See [formalization notes](../FORMALIZATION.md)
for the verified scope and the distinction between the unconditional iterative
construction and conditional results for the original two-stage route.
