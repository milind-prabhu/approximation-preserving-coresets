# PFR-style file dependency graph

Open the [live dependency graph](https://milind-prabhu.github.io/approximation-preserving-lean/),
or open `apc-dependency-graph.html` in a browser. It is self-contained and works
offline. Select a file to inspect its imports, theorem statements and complete
Lean source; select a theorem to jump to its declaration. Search, route filters,
zoom, pan, and SVG/DOT/data exports are included.

- 72 audited proof files, containing 367 checked named theorems.
- 118 direct local imports; 110 edges after transitive reduction.
- Arrows point from an imported prerequisite to the importing file.
- Green nodes are checked files; dark green double borders mark the two
  principal final-result files. Checked conditional statements remain conditional.
- Mathlib dependencies appear in the detail pane. Aggregate entry points and
  audit/scratch drivers are excluded.

These are **file imports**, not kernel-level lemma dependencies. A file may
import declarations that a particular theorem never uses. Reachability must not
be interpreted as a theorem's list of hypotheses. The graph also does not claim
that every assertion in the paper has been formalized; see the project README.

`apc-file-dependencies.pdf` and `.svg` provide vector versions of the whole
graph. The PNG is a raster preview. `dependency-data.json` contains the imports,
declarations, embedded sources and audited SHA-256 hashes.

To regenerate, install Python 3 and Graphviz, then run from the project root:

```sh
python3 dependency-graph/generate.py
```

The generator checks every source hash against `verification-summary.json`
and matches every named theorem against `final-audit.log`. It does not run Lean
again; the green status refers to that audited snapshot. It refuses to label
changed or unaudited sources as checked.

Visual references:

- [PFR blueprint graph](https://teorth.github.io/pfr/blueprint/dep_graph_document.html)
- [Terence Tao's blueprint tour](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/)

The PFR blueprint has declaration-level nodes. This adaptation groups the
checked declarations into file nodes, as requested.
