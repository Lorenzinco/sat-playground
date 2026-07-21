# Extension-guidance interpretation

This document describes how to interpret extension guidance for the pigeonhole and Tseitin encodings. The guidance system benchmarks whether the extensions selected naturally by DIP conflict analysis agree with a known proof strategy. It does not force the solver to select those extensions.

## Common model

Whenever conflict analysis finds a DIP pair `(a, b)`, the solver creates or reuses an extension variable:

```text
z <-> (a AND b)
```

The three defining clauses are:

```text
(z OR -a OR -b)
(-z OR a)
(-z OR b)
```

Immediately after obtaining the actual `z`, `cdcl.rs` calls the guidance tracker with:

```text
observe(a, b, z)
```

The actual value of `z` is used. This remains correct when preprocessing or unrelated extensions shift fresh-variable numbering, and when an existing extension variable is reused.

AND operands are commutative, so `(a, b)` and `(b, a)` are one canonical pair. Literal signs are not ignored:

```text
(a, b)
(-a, b)
(a, -b)
(-a, -b)
```

represent four different Boolean functions.

## What guidance does and does not do

Guidance currently operates in observation mode:

1. Conflict analysis selects a DIP from the implication graph.
2. The solver creates or reuses its extension variable.
3. Guidance checks whether that exact signed pair belongs to the expected proof structure.

The pair returned by `suggest()` is diagnostic. It is written to the optional log as `suggestion_before`, but it does not influence DIP selection.

A non-match therefore does not imply that the DIP is useless. It only means that the exact extension does not currently belong to the selected Cook or Tseitin guidance strategy.

# Common statistics

The formatted statistics contain:

```text
Guidance matches/checks
Guidance stages/depth
Guidance best progress
```

The same field names are used for two different strategies, so their exact interpretation depends on the reduction.

## Guidance checks

```python
stats.guidance_checks
```

The number of DIP events passed to `observe`.

If guidance is disabled, or if solving uses UIP and never creates a DIP extension, this is zero.

## Guidance matches

```python
stats.guidance_matches
```

The number of observed DIP events whose canonical signed operand pair belongs to at least one currently known guidance context.

Repeated observations count again. If the solver encounters the same correct pair ten times, it contributes ten matches.

The ratio:

```text
guidance_matches / guidance_checks
```

measures how frequently selected DIPs agree with the expected extension structure. It is not a proof-completion percentage.

## Guidance unique matches

```python
stats.guidance_unique_matches
```

The number of canonical matching pairs first observed while already recognized as valid.

Example:

```text
checks = 1012
matches = 51
unique_matches = 14
```

means:

- 1,012 DIP events were checked.
- 51 DIP events matched guidance.
- Those matching events involved 14 first-time canonical pairs.
- The other matching events reused previously observed pairs.

It does not mean that 14 proof paths were found.

An extension observed before its context exists may later be replayed when a dependency or child stage becomes available. That replay can advance guidance state, but it does not retroactively increment the earlier event's `matches` or `unique_matches` counters.

## Guidance stages completed

```python
stats.guidance_stages_completed
```

This field is strategy-specific:

- Pigeonhole: number of coherent pivot reductions completed.
- Tseitin: number of static AND-DAG nodes completed.

## Guidance deepest level

```python
stats.guidance_deepest_level
```

This field is also strategy-specific:

- Pigeonhole: deepest recursive PHP reduction level reached.
- Tseitin: deepest dependency level among completed circuit nodes.

## Guidance best progress

```python
stats.guidance_best_progress
```

- Pigeonhole: largest number of completed target cells in any coherent pivot context.
- Tseitin: number of completed static DAG nodes.

This is a raw count, not a normalized percentage.

# Pigeonhole guidance

## Original encoding

For `n` holes, the generator creates `n + 1` pigeons. Variables are row-major:

```text
x[pigeon, hole] = pigeon * n + hole + 1
```

Internally, rows and columns are zero-based.

The CNF contains:

1. One clause per pigeon requiring it to occupy at least one hole.
2. One binary clause per pair of pigeons and hole forbidding a collision.

```text
(x[p,0] OR ... OR x[p,n-1])
(-x[p,h] OR -x[q,h])
```

## Cook reduction represented by guidance

At a stage with `m` holes, the current literal matrix has dimensions:

```text
(m + 1) rows x m columns
```

Choose any pivot pigeon row `p` and any pivot hole column `h`.

For every non-pivot row `i` and non-pivot column `j`, define a collision gate:

```text
c[i,j] <-> matrix[i,h] AND matrix[p,j]
```

Then define a merge gate:

```text
d[i,j] <-> -matrix[i,j] AND -c[i,j]
```

The reduced PHP literal is:

```text
next_matrix[i,j] = -d[i,j]
```

This computes:

```text
next_matrix[i,j]
    = matrix[i,j] OR (matrix[i,h] AND matrix[p,j])
```

Completing every target for one pivot constructs:

```text
PHP(m+1,m) -> PHP(m,m-1)
```

## Valid first collision choices

Any two current matrix literals in different rows and different columns form a valid first Cook collision for two possible orientations.

Let:

```text
A = matrix[r1,c1]
B = matrix[r2,c2]
```

with:

```text
r1 != r2
c1 != c2
```

Then the two contexts are:

```text
pivot  = (r2,c1), target = (r1,c2)
pivot  = (r1,c2), target = (r2,c1)
```

The tracker retains both contexts until later merge choices distinguish them.

Same-row and same-column pairs are not Cook collisions. Negated or mixed-polarity versions are not exact Cook collisions either.

## Valid merge choices

After observing:

```text
c <-> matrix[i,h] AND matrix[p,j]
```

the corresponding ready merge is exactly:

```text
d <-> -matrix[i,j] AND -c
```

A merge with the wrong target literal, wrong collision variable, or wrong sign does not match that context.

## Coherent pivot progress

A fixed pivot at a stage with `m` holes has:

```text
m * (m - 1)
```

target cells.

Required target counts are:

| Holes at stage | Targets required for one pivot |
|---:|---:|
| 1 | 0; base case |
| 2 | 2 |
| 3 | 6 |
| 4 | 12 |
| 5 | 20 |
| 6 | 30 |

`guidance_best_progress` is the highest completed-target count in any one pivot context. To interpret it as a fraction, the stage width for that pivot must be known.

For example, at a five-hole stage:

```text
best_progress = 14
required = 20
coherent pivot progress = 14 / 20
```

Because recursive stages shrink, raw progress values from different depths are not directly comparable percentages.

## Completed stages versus one path

Every completed pivot spawns a child matrix and increments:

```python
stats.guidance_stages_completed
```

Several sibling pivots can complete at the same depth:

```text
                         PHP(5,4)
                    /       |       \
              pivot A    pivot B    pivot C
                 |          |          |
              PHP(4,3)   PHP(4,3)   PHP(4,3)
```

Therefore:

```text
stages_completed = 14
deepest_level = 1
```

can mean that 14 alternative first-level pivots completed. It does not mean a chain of 14 reductions was found.

## Complete PHP extension chain

For an original instance with `n` holes, the normalized Cook chain is:

```text
PHP(n+1,n)
-> PHP(n,n-1)
-> ...
-> PHP(3,2)
-> PHP(2,1)
```

The expected final depth is:

```python
expected_depth = reduction.size - 1
```

A complete extension chain exists when:

```python
stats.guidance_deepest_level == reduction.size - 1
```

Because child stages are only created from completed coherent parents, reaching that depth establishes that at least one coherent chain of Cook extension definitions reached `PHP(2,1)`.

It still does not prove that the solver derived every resolution clause of Cook's proof or that the final contradiction was obtained specifically through that chain. Guidance currently tracks extension definitions, not the complete resolution derivation.

## Ways to interpret PHP results

### Matches greater than zero, depth zero

The solver discovered individual Cook collisions or merges, but completed no pivot reduction.

### Best progress greater than zero, depth zero

At least one coherent pivot has merge outputs, but not all required target cells are complete.

### Many stages, depth one

The solver completed several alternative root pivots but did not recursively complete a child pivot.

### Depth greater than one

At least one coherent extension chain advanced recursively through multiple reduced PHP matrices.

### Depth equals `size - 1`

At least one complete Cook extension chain reached `PHP(2,1)`. This is the strongest PHP guidance result currently available.

### Many matches but few unique matches

The solver repeatedly selected the same small set of Cook-compatible DIPs. It is reusing correct gates more often than discovering new proof structure.

### Many unique matches but little best progress

The solver found gates from many incompatible pivot contexts. They are individually valid under some Cook path but do not combine into one advanced coherent pivot.

### Zero matches

The selected DIPs did not equal exact currently valid Cook gates. Typical PHP conflict graphs often produce same-hole, same-column, negative, or mixed-polarity pairs. Those may be useful CDCL extensions but are outside this normalized Cook strategy.

# Tseitin guidance

## Original encoding

The generator creates a connected cubic graph and assigns one odd charge. Every edge is represented by one SAT variable.

Each vertex receives CNF clauses enforcing:

```text
XOR(incident edge variables) = vertex charge
```

Because every edge occurs at two endpoints, XORing all vertex equations gives global edge parity zero. The odd total charge requires global parity one, producing the Tseitin contradiction.

## Static XOR circuit

Guidance describes one canonical static circuit. XOR is built from three supported AND extensions.

For literals `a` and `b`:

```text
both_false <-> -a AND -b
both_true  <->  a AND  b
xor_output <-> -both_false AND -both_true
```

This computes:

```text
xor_output = a XOR b
```

The generator constructs:

1. A left-associated XOR cascade for each vertex's incident edges.
2. A left-associated XOR cascade over all vertex parity outputs.

Different balanced circuits, vertex orders, XOR decompositions, or equivalent polarity choices are not currently recognized.

## Compact static DAG transport

The guidance contains:

```python
{
    "schema_version": 2,
    "kind": "static_and_dag",
    "original_variables": N,
    "operands": [[left, right], ...],
}
```

The planned result of node `i` is implicit:

```text
planned_result(i) = N + i + 1
```

At runtime, the actual solver variable can differ. The tracker maps each planned result to the actual `z` returned by DIP extension creation, then translates dependent nodes through that mapping.

This allows unrelated extensions and preprocessing to shift actual fresh-variable numbering.

## Ready static nodes

A static node is ready when every extension result referenced by its operands has already been mapped to an actual solver variable.

A DIP matches when its exact canonical signed pair equals a ready node's translated actual operands.

If the same pair is observed before the node becomes ready, the tracker stores the unique observed definition and can replay it when dependencies activate.

## Tseitin stages completed

For static guidance:

```python
stats.guidance_stages_completed
```

is the number of completed AND-DAG nodes, not the number of full parity equations or proof stages.

The total expected node count is:

```python
total_nodes = len(reduction.extension_guidance["operands"])
```

A complete static extension circuit is present when:

```python
stats.guidance_stages_completed == total_nodes
```

## Tseitin depth

Each static node has a dependency level:

```text
level 1: operands use only original edge variables
level 2: depends on at least one level-1 extension
level 3: depends on deeper extension results
...
```

```python
stats.guidance_deepest_level
```

is the maximum dependency level among completed nodes.

A large number of completed level-1 nodes with depth one means that many independent first gates were found, but no deeper XOR cascade was completed.

## Tseitin best progress

For static guidance:

```python
stats.guidance_best_progress
```

is currently the total number of completed DAG nodes. It is usually equal to `guidance_stages_completed`.

The useful normalized fraction is:

```python
completed = stats.guidance_stages_completed
total = len(reduction.extension_guidance["operands"])
fraction = completed / total
```

## Complete Tseitin circuit versus complete proof

Completing every static DAG node means the solver found all extension definitions in the selected parity circuit.

It does not by itself mean that the solver derived:

```text
global parity = 1
```

from the charges and:

```text
global parity = 0
```

from edge cancellation using the expected resolution derivation. The current tracker checks the extension scaffold, not every subsequent resolution clause.

## Ways to interpret Tseitin results

### Some matches, depth one

The solver found independent first-level gates but did not naturally continue the expected XOR cascades.

### Increasing depth

The solver is capturing dependent XOR gates in the intended order, with actual extension-variable mapping working across the cascade.

### Completed nodes less than total

Only part of the canonical parity circuit was found.

### Completed nodes equal total

The complete canonical extension circuit was captured. This is not yet proof that the expected resolution contradiction was completed.

### Many matches but few unique matches

The solver repeatedly reused a small subset of expected gates.

### Zero matches

Natural DIP selection chose gates outside the one canonical XOR circuit. Equivalent XOR associations or decompositions are not treated as exact matches.

# Guidance log interpretation

With `extension_guidance_log_path` enabled, each DIP line has the form:

```text
dip actual=(a, b)->z
    canonical=(min, max)
    matched=true|false
    unique=true|false
    contexts=k
    stages_completed_now=k
    active_progress=k
    best_progress=k
    stages_completed_total=k
    deepest_level=k
    suggestion_before=...
```

## `actual=(a, b)->z`

The exact DIP operands and actual returned extension variable.

## `canonical=(min, max)`

The commutative key used by the tracker. Ordering changes are ignored; signs are preserved.

## `matched`

Whether the pair belongs to at least one currently known exact guidance context after processing the observation.

## `unique`

Whether this was the first observation of the canonical pair and it matched at that time.

## `contexts`

The number of guidance contexts supported by the pair.

For PHP, a first diagonal collision commonly has two contexts because either opposite corner may identify the pivot orientation. A pair can support more contexts after multiple stages exist.

For Tseitin, this is the number of static nodes represented by the ready pair. The static builder normally deduplicates identical gates, so this is commonly one.

## `stages_completed_now`

The number of PHP pivot reductions or static DAG nodes completed by this observation, including completions unlocked through replay.

## `active_progress`

Current progress among active, unspawned PHP pivots, or current completed-node count for static guidance. PHP active progress may decrease after a pivot completes because that pivot is no longer active.

## `best_progress`

The maximum progress reached at any time. Unlike active progress, it does not decrease.

## `stages_completed_total`

Cumulative completed PHP pivots or static nodes.

## `deepest_level`

Deepest PHP recursion or static dependency level reached so far.

## `suggestion_before`

A deterministic exact pair that would advance the currently preferred guidance context. It is computed before observing the actual DIP and is diagnostic only.

For PHP, suggestions prioritize:

1. A ready merge.
2. A missing collision in the deepest, most advanced coherent pivot.
3. A first collision in the deepest available non-base stage.

For static guidance, the suggestion is the first ready DAG node in deterministic order.

# Common interpretation mistakes

## "Matches means complete proof steps"

No. Matches count DIP events whose extension definitions agree with guidance.

## "Unique matches means unique proof paths"

No. They are unique canonical literal pairs.

## "Stages completed means recursive depth"

No. Many sibling PHP pivots can complete at one depth, and static stages are individual DAG nodes. Use `guidance_deepest_level` for depth.

## "Best progress is a percentage"

No. It is a raw target or node count.

## "Ignoring signs would reveal more correct matches"

It would reveal structurally related variable pairs, but not necessarily equivalent Boolean functions. Exact guidance intentionally preserves signs.

## "A complete extension circuit proves UNSAT"

No. It proves that the expected extension-variable scaffold was captured. The solver must still derive the necessary resolution clauses and contradiction.

## "Zero matches means DIP learning failed"

No. It means the selected DIPs did not match this proof strategy. They may still improve CDCL through a different extended-resolution path.

# Recommended benchmark report

For every run, record at least:

```text
problem
problem size
DIP extensions created
guidance checks
guidance matches
guidance unique matches
guidance match rate
guidance stages completed
guidance deepest level
guidance best progress
solver conflicts
solver runtime
```

For PHP, additionally derive:

```python
complete_chain = stats.guidance_deepest_level == reduction.size - 1
```

For Tseitin, additionally derive:

```python
total_nodes = len(reduction.extension_guidance["operands"])
complete_circuit = stats.guidance_stages_completed == total_nodes
completion_fraction = stats.guidance_stages_completed / total_nodes
```

Keep these conclusions separate:

1. The solver found individual expected gates.
2. The solver advanced one coherent context.
3. The solver completed the expected extension scaffold.
4. The solver completed the expected resolution proof.

The current guidance directly measures the first three at different strengths. It does not yet certify the fourth.
