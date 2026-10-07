# JSP-000076 — Subset Sum 2-Coloring Lean Formalization

> **Problem**: Sparsest Rado set (2-color complete additive basis)
> **Statement**: any 2-color complete set A satisfies |A ∩ [1,N]| ≥ N^{1/2 + o(1)}
> **Solver**: Cilleruelo-Goldstern-Mata (2021, arxiv:2104.14766), building on Sárközy-Erdős 1985
> **JSP bounty**: USD $100
> **Current status**: Solved, Lean proof: No, Eligible: No

## Build

```sh
lake build
```

## Attribution

Original Lean code by `skj-pixel`. Reference: Cilleruelo, Goldstern, Mata
(2021) "Subset sums, completeness and colorings" arXiv:2104.14766.

## Plan

1. ✅ Outer statement scaffold
2. (TODO) Sumset structure theorems (Plünnecke-Ruzsa type)
3. (TODO) Lower bound on |A ∩ [1,N]| via Sidon-set density
4. (TODO) Assemble → cilleruelo_goldstern_mata_2021 → jsp_000076
