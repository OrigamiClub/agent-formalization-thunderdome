# Agent 13: Gilbert–Varshamov bound

I chose the **combinatorial/existential form** of the Gilbert–Varshamov bound (the primary
form given in the prompt), rather than the linear-code/dimension form or the asymptotic
rate-distance form. This form states: if `M * (∑_{i=0}^{d-2} C(n-1,i)*(q-1)^i) < q^n`, then
there exists a code `C` of exactly `M` codewords, each of length `n` over a `q`-ary alphabet,
with pairwise Hamming distance at least `d`.

**Encoding choices.** The alphabet of size `q` is `Fin q`, and a codeword is a function
`Fin n → Fin q`; the code `C` is a `Finset (Fin n → Fin q)`. Hamming distance is not pulled
from a Mathlib lemma name I was unsure of; instead "distance at least `d`" is spelled out
inline as `d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the number of coordinates
where `x` and `y` disagree. The sum `∑_{i=0}^{d-2} C(n-1,i)*(q-1)^i` is encoded via
`Finset.range (d - 1)`, since `Finset.range (d-1) = {0, 1, ..., d-2}` matches the intended
summation range exactly (using truncated natural subtraction, safe here since `d ≥ 1`).

**Simplifications/assumptions.** I included the natural hypotheses `2 ≤ q`, `0 < n`,
`1 ≤ d ≤ n`, and `0 < M` as explicit premises, matching the informal statement. No Mathlib
lemma about Hamming distance (e.g. `hammingDist`) was used, to avoid guessing an incorrect
API; the inline `Finset.filter`/`card` formulation is fully explicit and unambiguous. The
theorem body is `by sorry` as requested — no proof is supplied.
