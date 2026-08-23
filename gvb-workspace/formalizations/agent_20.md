# Gilbert–Varshamov bound — agent_20

**Form chosen:** the direct combinatorial/existential form (the first form given in
the prompt), not the linear-code/dimension form or the asymptotic rate-distance form.
It states: given alphabet size `q ≥ 2`, length `n ≥ 1`, target distance `1 ≤ d ≤ n`,
and a positive integer `M` satisfying `M * Σ_{i=0}^{d-2} C(n-1,i)(q-1)^i < q^n`, there
exists a set of codewords of size `M` with pairwise Hamming distance `≥ d`.

**Encoding choices.** Codewords are modeled as functions `Fin n → Fin q` (the standard
Mathlib-style representation of length-`n` strings over a `q`-letter alphabet), and the
code itself is a `Finset (Fin n → Fin q)`. Rather than invoking a dedicated Hamming
distance function (I was not confident of the exact Mathlib name/API for it), I define
the "distance ≥ d" condition inline as `d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`,
i.e. the number of coordinates where two codewords differ is at least `d`. The sum
`Σ_{i=0}^{d-2} C(n-1,i)(q-1)^i` from the background is written as
`∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, using natural-number subtraction
(`d - 1` gives indices `0,…,d-2` since `Finset.range (d-1) = {0,...,d-2}`).

**Uncertain identifiers:** `Finset.filter` with a decidable predicate on `Fin n` should
type-check automatically via `DecidableEq (Fin q)`; I avoided relying on `Nat.choose`'s
exact namespace beyond the standard `(n-1).choose i` dot-notation, which I believe is
correct. No proof is attempted (`sorry`).
