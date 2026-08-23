# Agent 18: Gilbert–Varshamov bound

**Form chosen:** the combinatorial/existential form given as the primary statement in the
prompt (Varshamov's sphere-packing-style bound), not the linear-code/dimension form and not
the asymptotic rate-distance (entropy) form. Codewords are represented as functions
`Fin n → Fin q` (an alphabet of size `q`, block length `n`), and a code is a `Finset` of such
functions. Hamming distance between two codewords is Mathlib's `hammingDist`, which unfolds to
the cardinality of the set of coordinates where the two functions disagree — this is exactly
"differ in at least `d` coordinates" when we require `d ≤ hammingDist x y`.

**Encoding choices:** the sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as
`∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, so that `i` ranges over
`0, …, d-2` and the sum is (conventionally) `0` when `d = 1`, matching standard empty-sum
semantics. Natural-number subtraction (`n - 1`, `d - 1`, `q - 1`) is safe given the hypotheses
`n ≥ 1`, `d ≥ 1`, `q ≥ 2`. The conclusion asserts existence of a `Finset` `C` with `C.card = M`
and pairwise Hamming distance at least `d` among distinct elements, which is the direct
Lean/Mathlib rendering of "there exists a code of size `M` with minimum distance ≥ `d`".

**Identifiers I was not 100% certain of:** `hammingDist` (from `Mathlib.InformationTheory.Hamming`) —
I am fairly confident of its name and signature (`hammingDist : (∀ i, β i) → (∀ i, β i) → ℕ`
requiring `Fintype ι` and `DecidableEq (β i)`), but could not check it against a compiler.
