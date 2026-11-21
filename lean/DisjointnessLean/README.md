# Lean 4 companion to *Unconditional Boolean Dynamic Lower Bounds from Disjointness*

This project formalizes the Disjointness lower bound and its applications. The reference for this edition is the supplied *Unconditional Boolean Dynamic Lower Bounds from Disjointness* manuscript (`main.tex` with its three included sections). The paper studies a family of $n$ arbitrary subsets of an $n$-element universe. A fixed sequence of insertions builds a set $X$, and a final query asks whether $S_q$ and $X$ are disjoint.

## Main result

`DisjointnessDraft.Native.main` proves the main theorem by the draft's sparse-set communication argument. The explicit constant is available as `DisjointnessDraft.Native.explicit_tradeoff`. For every fixed pair of positive constants bounding the ratio of word size to `log₂ n`, and all sufficiently large $n$, it proves

```text
t_q ≥ (1 / 100000) · (log₂ n / log₂(t_u · w))².
```

The hypotheses require zero error on every tape, a worst-case update bound, measurable running times and an expected query bound on every fixed family, update sequence and final query. The update budget $t_u$ is an integer. Both time bounds are at least one, as in the draft. `DisjointnessDraft.Native.maximum` derives the stated lower bound on the larger of the two operation times. The application lower bounds use the same native proof, including a version for histories with distinct insertions. The convenience name `DisjointnessDraft.main` refers to the same native theorem.

## How to check the release

In the extracted project directory, with Lean's toolchain manager and Git available, run

```sh
lake exe cache get
lake build DisjointnessDraft
lake env lean CheckDisjointnessDraft.lean
```

On macOS installations that cannot launch the compiled cache helper, `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get` runs the same downloader through the interpreter.

The toolchain is Lean 4.19.0. Lake uses the dependency revisions in `lake-manifest.json`, including mathlib and PFR. The archive includes the project sources and its local `DisjointnessFoundations` library. An initial installation needs access to the pinned dependencies. `DisjointnessDraft.lean` imports the project. The last command examines theorem dependencies transitively and fails on any axiom outside `propext`, `Classical.choice` and `Quot.sound`. It also checks that the main theorem and the listed application lower bounds use the physical simulation, communication bound and sparse product-corruption theorem. An unfinished proof using `sorryAx` fails the audit.

## Main proof and preliminaries

All names in the tables are relative to the namespace `DisjointnessDraft` unless a different namespace is given. Module paths in the archive follow the same directory structure.

| Part of the manuscript | Lean entry points | What the proof checks |
| --- | --- | --- |
| Cell-probe conventions and main theorem | `MainBound`, `Native.main`, `Native.maximum` | Random tapes, preprocessing, histories, expected query cost, all sufficiently large sizes and the logarithmic tradeoff. |
| Hard distribution and parameters | `Native.intersection_expectation`, `Native.true_frequency`, `Native.depth_twenty`, `Native.large_epoch`, `Native.log_geometry` | Independent uniform fixed-size subsets in disjoint blocks, intersection probabilities, selection of epochs and their sizes. |
| Fixing the random tape | `Native.fix_tape`, `Native.exact_trace`, `Native.full_budget` | One tape works for the joint finite hard input distribution. Distinct epoch cells read by the full query are charged to its actual work. |
| Simulation and verification | `Native.verified_bit`, `Native.physical_lower`, modules `Simulation.Tables` and `Simulation.Lengths` | The verified bit agrees with the data structure's true answer. Finite tables encode the advice and messages. `Native.physical_full` gives the finite success bound with the actual full-query epoch count. `Native.subpolynomial` proves the little-o success corollary. |
| Conditional information identities | `Information.direct_sum`, `.process`, `.drop_condition` and `.independent_condition` | Chain rule for a family of observations, processing an observation, and the two rules for adding a conditioning variable. |
| Information bounds on accepted views | `Information.Game.query_entropy_bits`, `.update_entropy_bits`, `.accepted_correlation`, `.fiber_conclusions` and `.NearWitness.rectangle` | Query smoothing and update atom bounds hold on at least three quarters of the accepted views. The selected joint distribution and its independent marginals yield the draft’s near-rectangle and rectangle. |
| Direct sum and transcripts | Modules `Information.DirectSum`, `Information.Charges`, `Information.Leakage` | Query-side information, update-side guessing probabilities, and correlation after conditioning on an accepted disjoint answer. |
| Smoothing, near-rectangles, and communication | `Information.smoothing`, `Information.near_rectangle`, `Information.product_rectangle`, `Information.rectangle_cost`, `Information.communication_bound` and module `Information.PhysicalUpper` | Conditional distributions, independent marginals, entropy deficits and the upper bound on acceptance used in the contradiction. |
| Finite KL divergence and average min-entropy | `Information.RelativeEntropy.chain`, `Information.MinEntropy.reveal`, `.tail`, `.coarsen` and `.event` | The KL chain rule includes infinite divergence and zero-mass conditioning rows. Optimal guessing probabilities give the average conditional min-entropy inequalities. |
| Flat distributions and rectangles | `Information.Flat.decompose`, `Information.Flat.rectangle` | Every capped finite probability vector is a mixture of uniform $K$-element subsets. Taking products gives the corresponding rectangle decomposition. |
| Binomial and counting estimates | `Corruption.Binomial.choose_bound`, `.entropy_tail`, `.incidence` and `.avoidance` | The printed entropy bound for a binomial tail and both uniform-subset probability inequalities. |
| Sparse-set corruption | `Corruption.uniform_corruption`, `Corruption.product_corruption`, `Corruption.min_entropy_corruption` | The bound $s^2/(100N)$ for $s\ge 200$, positive $N$, and $s^2\mid N$, including nonuniform independent marginals under the atom caps. `Corruption.uniform_source_chain` proves the ordered good-row and fresh-piece claim in the manuscript. The product proof finishes with an exponential moment and the atom caps directly. The flat-decomposition argument is also available separately. |

## Applications

The application theorems quantify over the target data structure and its operation costs. If the reduction answers the source query using only target queries, the lower bound applies to $t_q$. If it also performs target updates, the bound applies to $t_u+t_q$. Both imply that $\max(t_u,t_q)$ is at least a constant times $(\log N/\log\log N)^2$.

| Application | Lean entry points |
| --- | --- |
| Transfer | `Transfer.polynomial` transfers any faithful, costed simulation under two-sided polynomial size distortion. `Transfer.Compiler.polynomial` and `Transfer.Compiler.rel_lower` compile finite target scripts into a word-probe machine. `Transfer.Auxiliary.polynomial` accounts for reads and writes to a separate word array used to select the target operations. `Transfer.Auxiliary.interleaved_polynomial` permits report-dependent auxiliary probes throughout a fixed sequence of target operations. The relational version admits any valid query report on each execution. `Transfer.Compiler.init_guarantees` accounts for the memory and operation count after preprocessing a target that starts empty. |
| Directed reachability, including a fixed sink or fixed source on depth-two DAGs | `Reachability.directed` and `Reachability.fixed_source`. `Applications.BooleanTargets.graphs` explicitly includes targets whose queries write to memory. |
| Fixed-pair reachability, directed cycle detection, strong connectivity of a pair, number of strongly connected components, size of the largest strongly connected component, and undirected triangles | `Applications.GraphCosts.lower` with `fixedReach`, `cycleDetection`, `pairScc`, `sccCount`, `largestScc` or `triangles` in the same namespace. |
| Number reachable from a fixed source | `Applications.ReachCount.lower`. A second count after a fresh edge to the sink eliminates the need for a separate table of row sizes. |
| Undirected shortest paths and nearest marked vertex | `Applications.DistanceLower.lower` covers numeric reports for fixed-source distance (factor below 2), fixed-pair distance (factor below 5/3) and distance to the nearest marked vertex (factor below 3). Disconnected pairs have infinite distance. |
| Subgraph connectivity | `Applications.SubgraphCosts.lower` covers incremental vertex activation. Both queried vertices must be active, including for a length-zero path. |
| Bipartite matching | `Applications.MatchingGraph.lower` covers maximum size at every sufficiently large vertex count and perfect matching at sufficiently large even counts. With an odd number of vertices the perfect-matching answer is always false. |
| Exact densest subgraph | `Applications.Density.density_iff` proves the threshold equivalence. `Applications.DensityGraph.lower` gives the physical bounds for both exact and threshold queries on an unrestricted simple graph starting empty. |
| Planar shortest paths, positive integer or unit weights | `Applications.PlanarTarget.lower` and `Applications.UnitTarget.lower` give the exact-distance and fixed-threshold bounds from an empty graph, with an explicit crossing-free drawing and exactly $N$ vertices. |
| Diameter of connected planar graphs | `Applications.DiameterGraph.lower` covers exact diameter and a fixed threshold while keeping the graph connected at every update. `Applications.DiameterEmpty.lower` starts with an empty graph and requires connectivity whenever a query occurs. The physical reduction uses two permanent fallback edges to maintain connectivity. Its padding leaves increase the calibrated threshold by one. `Applications.OriginalDiameter.diameter` separately verifies the printed formula $2L+D-f_q$ for the draft’s full two-fan construction, with its stated vertex count. |
| Directed girth of planar graphs | `Applications.WeightedGirth.lower` and `Applications.UnitGirthNative.lower` cover exact girth and threshold queries. The unit-weight version inserts edges by specifying just their endpoints. |
| Planar maximum-weight bipartite matching | `Applications.MatchingLower.lower` and `.planar_lower` give the exact optimum and fixed-threshold queries starting from an empty graph. The hard instance uses positive integer weights at most $N$. |
| Shared planar constructions | `Applications.OriginalGrid`, `Applications.PlanarCore.distance`, `Applications.Planarity`, `Applications.UnitCore.distance`, `Applications.DirectedCore.girth`, `Applications.PlanarMatching.maximum` and `Applications.CoreSize` contain the grid distance, plane drawing, subdivision, girth, matching optimum and finite size calculations. `Applications.UnitLabels.cardinality` gives $11p^3+6p^2+2p$ for the actual subdivided graph before padding. |
| Set disjointness, Langerman, Pagh, Erickson and range mode | `Applications.SetDisjointness.lower`, `Applications.Langerman.lower`, `Applications.Pagh.lower`, `Applications.Erickson.lower` and `Applications.RangeMode.lower`. `Applications.BooleanTargets.sets` includes writable set-disjointness queries. The Langerman theorem applies to bounded integer inputs and assignments. The Erickson bound already holds for Boolean initial matrices and short histories. The range-mode theorem uses realized endpoints and allows arbitrary choices between tied modes. `Applications.Arrays.range_mode` checks the count argument for the printed interval. The physical reduction uses a fixed signal value so the decoder needs no row metadata. |
| Nonsingular matrices over prime fields | `Applications.MatrixStringLower.matrices` covers inverse-entry zero testing, inverse-entry reporting, testing whether the determinant is one, and determinant reporting. The theorem applies to every prime $p$ with $N\le Kp$ for a fixed $K$, in particular to the stated $p=\Theta(N)$ families. |
| Maximal points and distinct colors | `Applications.MaximaCosts.lower` and `Applications.GeometricCosts.lower` cover the actual counts and bound every coordinate by a polynomial. Some scripts use a second copy of a row as a control for comparisons. |
| Three-dimensional convex-hull vertex count | `Applications.HullClassification.robust` proves the full extreme-point classification under perturbation, `.snapped` verifies the integer-grid rounding and `.integer_lower` gives the unconditional physical lower bound. |
| Internal dictionary matching, active documents, binary Hamming threshold and exact Hamming distance | `Applications.MatrixStringLower.strings` gives the physical lower bounds after padding the string lengths or budgets. |
| Streaming regular-expression membership | `Streaming.selector_lower` and `Streaming.some_symbol` give the selector and worst-symbol bounds. `Streaming.Storage.upper` checks a deterministic matcher and its total cost on every stream. `Streaming.PackedTable.scan_equivalence` verifies that packing n² incidence bits into ⌈n²/w⌉ words preserves the selector scan’s result and exact probe count, with 2n+2 mutable addresses. The complete matcher proof uses the straightforward word-per-entry layout. `Streaming.Binary.Indexed.uniform_lower` gives the bit-level lower bound after binary encoding, with arbitrary master tapes and access to the current bit position. `Streaming.Binary.BitStorage.separation_upper` checks constant amortized cost on every binary input stream. |

## Reading the model

The lower bound concerns the maximum over fixed inputs of the expected query cost. A probability-space parameter represents the entire random tape, so the sections that compile several target operations explicitly preserve their dependence on past operations. The query-compilation proofs charge clock storage and handle writes made by a value-returning query. The hard instances use finite structures. The machine assumptions quantify over all legal histories in the stated target problem.

`Transfer.Auxiliary.polynomial` covers a controller that reads its auxiliary words before issuing a target batch. `Transfer.Auxiliary.interleaved_polynomial` also permits auxiliary reads and writes between target calls or after the final report. For each fixed source input and query, all allowed target reports must induce the same legal target operation sequence. Auxiliary probe addresses may depend on earlier reports. The controller pays for auxiliary probes, and the target's fixed-history guarantees pay for target calls. The APIs accept typed operation arguments. Their word-size bounds depend on the application and encoding.

The entries describe mathematical statements. Historical comparisons, priority claims and bibliographic attributions in the draft are outside the proof statements.
