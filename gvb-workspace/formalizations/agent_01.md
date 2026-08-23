# Agent 01: Gilbert–Varshamov bound

**Form chosen:** the combinatorial/existential form (primary form given in the prompt) —
"if `M * (sum_{i=0}^{d-2} C(n-1,i) (q-1)^i) < q^n` then there exists a code of size `M`
with minimum Hamming distance `≥ d`." This was chosen over the linear-code/dimension
form and the asymptotic rate-distance form because it is the most directly
combinatorial statement and translates cleanly into `Finset`/`Fintype` language
without needing a `FiniteField` or an asymptotic limit.

**Encoding choices:** the alphabet of size `q` is `Fin q`, and a codeword of length `n`
is a function `Fin n → Fin q`; codes are `Finset (Fin n → Fin q)`. I used Mathlib's
`hammingDist` (from `Mathlib.InformationTheory.Hamming`), which I believe is defined as
`(Finset.univ.filter fun i => x i ≠ y i).card` on such Pi-types — i.e. exactly the number
of differing coordinates — though I did not have a compiler to confirm the exact name/
signature, so this is a best guess. The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is encoded as
`∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, since `Finset.range (d-1) = {0,...,d-2}`
matches the upper limit `d-2` exactly (assuming `d ≥ 1`, i.e. `d - 1` is not degenerate).

**Hypotheses:** `q ≥ 2`, `n > 0`, `1 ≤ d ≤ n`, `M > 0`, plus the GV inequality itself, matching
the natural-language statement given. The conclusion asserts existence of a `Finset` `C` of
codewords with `C.card = M` such that every two distinct codewords in `C` have Hamming
distance at least `d`.

**Uncertainties:** the exact Mathlib identifier/namespace for `hammingDist` and its argument
order/implicit-instance requirements (decidable equality on `Fin q`, `Fintype` on the domain)
are my best recollection, not verified against a compiler.
