# Lean formalizations: dynamic Boolean lower bounds from Disjointness

This repository contains Lean 4 formalizations of two papers by Young Kun Ko, together with their LaTeX sources.

| Paper | Sources | Lean |
| --- | --- | --- |
| *Unconditional Boolean Dynamic Lower Bounds from Disjointness* ([arXiv:2610.10904](https://arxiv.org/abs/2610.10904)) | [`human-proofs/Disjointness`](human-proofs/Disjointness) | [`lean/DisjointnessLean`](lean/DisjointnessLean) |
| *Amortized Cell-Probe Lower Bounds for Dynamic Boolean Problems* ([arXiv:2611.11508](https://arxiv.org/abs/2611.11508)) | [`human-proofs/AmortizedBound`](human-proofs/AmortizedBound) | [`lean/AmortizedBound`](lean/AmortizedBound) |

Main theorems:

- `DisjointnessDraft.Native.main` (`DisjointnessDraft.MainBound`): every zero-error data structure for insert-only multiphase Disjointness with m = n sets, word size Θ(log n), worst-case update time t_u and expected query time t_q has t_q = Ω((log n / log(t_u w))²). `DisjointnessDraft.Native.maximum` gives max(t_u, t_q) = Ω((log n / log log n)²). The applications are listed in [`lean/DisjointnessLean/README.md`](lean/DisjointnessLean/README.md).
- `AmortizedBound.total_work`: Ω(n (log N / log log N)²) expected total probes on a fixed distribution of n = ⌊N^{1/4}⌋ insertions, each followed by a query, with per-query error 2⁻¹².
- `AmortizedBound.query_tradeoff`: t_q = Ω((log N / log(t_u w))²) for amortized insertion time 1 ≤ t_u = N^{o(1)} and constant error, with one constant for all such t_u. The graph corollaries are in `AmortizedBound.GraphCorollaries` and `AmortizedBound.TriangleCorollary`. See [`lean/AmortizedBound/Amortized-verification.txt`](lean/AmortizedBound/Amortized-verification.txt).

All results depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Building

You need [elan](https://github.com/leanprover/elan) and Git. The toolchain is Lean 4.19.0. Mathlib (v4.19.0) and PFR are pinned in `lean/DisjointnessLean/lake-manifest.json`.

```sh
cd lean/DisjointnessLean
lake exe cache get                     # downloads prebuilt mathlib
lake build                             # the Disjointness formalization
lake env lean CheckDisjointnessDraft.lean   # axiom and dependency audit

# the amortized bound, built on top of the same project
lake env lean --root=../AmortizedBound -o .lake/build/lib/lean/AmortizedBound.olean ../AmortizedBound/AmortizedBound.lean
lake env lean ../AmortizedBound/CheckAmortized.lean
```

Without the mathlib cache, `lake build` compiles mathlib from source, which takes a few hours.

## License

The Lean code is released under the Apache License 2.0 (see [`LICENSE`](LICENSE)), the same license as mathlib. The paper sources in `human-proofs/` are copyright the author.
