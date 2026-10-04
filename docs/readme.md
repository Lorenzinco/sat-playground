# Sat-Playground

This repository was born in effort of benchmarking different ideas with my solver on hard combinatorial instances.

![GitHub License](https://img.shields.io/github/license/Lorenzinco/sat-playground?logo=gnu&logoColor=rgb(255%2C255%2C255))

# Installation

Sat-playground can be executed directly from the python interface exposed, to compile and use the class first create a venv.

```bash
python -m venv .venv && source .venv/bin/activate
```

After that install maturin, there are different methods, follow whichever you like, please refer to the official ![docs.](https://www.maturin.rs/installation.html)

After installing you're ready to build and use the class provided by the python interface.

To build 
```bash
maturin develop --release
```

After building you're pretty much ready to go, please refer to the `main.py` file found inside the repository for an example on how to use the class.

## Conflict analysis and history

History uses a flat assignment trail with decision-level boundaries and
variable-indexed reasons and levels. Backtracking retains buffer capacity and
returns the removed reasons without allocating a new vector.

UIP analysis walks the trail without building a graph. DIP reuses a compact CSR
implication graph for exact two-vertex separator selection, then extracts the
post clause from cached predecessors and lower-level literals instead of walking
reasons again. Analysis, separator search, clause minimization, and LBD computation
reuse scratch buffers. DIP still requires at most one nonroot lower level in its
post clause; unavoidable violations are rejected before separator search.
These early rejections count as `dip_lbd_rejections`, not `dip_candidates_found`.

## Clause vivification

CDCL supports opt-in clause vivification with `"vivification"` (or its alias
`"vivify"`) in the `preprocess` or `inprocessing` list passed to `Sat.solve`.
Inprocessing vivification runs on the ordinary inprocessing restart schedule,
not on every solver call or every GES pass. When BVA is enabled it runs before
BVA, preserving the preference pass immediately before BVA if also enabled.
Neither phase enables vivification by default. For example:

```python
solver.solve(
    algorithm="cdcl", implication_point="dip", heuristics="vsids",
    preprocess=[], inprocessing=["vivification", "bva", "ges"],
)
```

The implementation follows the candidate-excluding probing and reason-analysis
approach in [Kissat](https://github.com/arminbiere/kissat/blob/master/src/vivify.c)
and [CaDiCaL](https://github.com/arminbiere/cadical/blob/master/src/vivify.cpp).
It shares the solver's two-watched-literal propagation core, but probing does not
update search utility or GES usage statistics. One reusable temporary decision
level holds the assumptions; it is rolled back before replacements or interruption
checks. Strengthened clauses are logged before their sources are deleted.
Extension definitions (`lbd == 0`) and active implication reasons are not candidates.

Each pass considers at most 256 candidates from a rotating 4,096-slot window,
prioritizes low-LBD learned clauses, and probes copied literals in descending
occurrence order. Candidates have 3–32 literals. Probe/analysis work is limited to
50,000 ticks per pass and 4,096 per candidate; a propagation tick counts a visited
watch entry or inspected clause literal. Analysis steps also consume ticks. A
propagation limit can overshoot by one clause scan. These are conservative initial
limits, not benchmark-tuned defaults. Root closure and candidate selection are
outside that probe budget.

Unlike the full upstream implementations, this version only performs strict
subset strengthening: it does not reuse assumption prefixes between candidates,
perform final-literal instantiation, or delete whole clauses based on implication.
It preserves original/essential clause status and transfers GES provenance when
strengthening an existing GES replacement.

`Sat.stats` exposes read-only counters: `vivification_passes`,
`vivification_clauses_tried`, `vivification_clauses_strengthened`,
`vivification_literals_removed`, `vivification_propagation_ticks`,
`vivification_budget_exhaustions`, and `vivification_units`.