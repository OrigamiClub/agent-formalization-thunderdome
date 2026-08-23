# Agent 03: Gilbert–Varshamov bound

**Form chosen:** the classical combinatorial/existential form (the primary
form given in the prompt), not the asymptotic rate-distance (entropy)
form and not the linear-code/dimension form. I.e.: given alphabet size
`q ≥ 2`, length `n ≥ 1`, target minimum distance `1 ≤ d ≤ n`, and a target
code size `M ≥ 1`, if `M * (∑_{i=0}^{d-2} C(n-1,i)(q-1)^i) < q^n`, then a
code of exactly `M` codewords over the `q`-ary alphabet of length `n`
exists with pairwise Hamming distance at least `d`.

**Encoding choices:**
- The alphabet is `Fin q` and codewords are elements of `Fin n → Fin q`
  (the full `q`-ary space, of cardinality `q^n`, matching the RHS of the
  bound directly rather than invoking `Fintype.card`).
- A code is a `Finset (Fin n → Fin q)`; the existence claim asserts a
  finset `C` with `C.card = M` and the "distance ≥ d" property holding
  for every pair of *distinct* elements of `C`.
- Hamming distance uses Mathlib's `hammingDist` (from
  `Mathlib.InformationTheory.Hamming`), which I believe counts the number
  of coordinates where two dependent functions differ; I was not 100%
  certain of the exact Mathlib name/signature, so this is a best guess
  and flagged as such.
- The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is encoded as
  `∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, using natural
  number subtraction; `Finset.range (d-1) = {0,...,d-2}` matches the
  intended index range exactly (and correctly degenerates to the empty
  sum, value 0, when `d = 1`).
- No proof is attempted; the theorem body is `by sorry`.
