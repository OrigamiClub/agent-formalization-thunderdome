# Agent 08: Gilbert–Varshamov bound

**Chosen form:** the combinatorial/existential (finite, non-asymptotic) version — the primary
form given in the prompt, not the rate-distance asymptotic or linear-code/dimension variants.
Given alphabet size `q ≥ 2`, length `n > 0`, target minimum distance `1 ≤ d ≤ n`, and a target
code size `M > 0` satisfying `M * (∑_{i=0}^{d-2} C(n-1,i) * (q-1)^i) < q^n`, the theorem asserts
existence of a `Finset` of codewords `C : Finset (Fin n → Fin q)` with `C.card = M` in which
every two distinct codewords have Hamming distance at least `d`.

**Encoding choices:**
- The alphabet of size `q` is modeled as `Fin q`; a codeword is a function `Fin n → Fin q`, so
  the ambient space `Fin n → Fin q` has cardinality `q^n`, matching the right-hand side of the
  bound.
- The left-hand sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` (the volume of a Hamming ball of radius
  `d-2` in the (n-1)-sphere, standard in GVB proofs via the greedy/sphere-packing argument) is
  written as `∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i`, since
  `Finset.range (d-1) = {0, ..., d-2}` for `d ≥ 1`.
- Hamming distance is expressed via the Mathlib identifier `hammingDist` (from
  `Mathlib.InformationTheory.Hamming`), which for `x y : ∀ i, β i` is defined as
  `(Finset.univ.filter fun i => x i ≠ y i).card` — exactly "number of differing coordinates."
  I was not 100% certain this identifier applies directly to plain `Fin n → Fin q` functions
  (as opposed to only the `Hamming`-wrapped type synonym); if it turns out not to unify
  directly, the intended fallback is the equivalent inline definition
  `(Finset.univ.filter fun i => x i ≠ y i)).card` in place of `hammingDist x y`.
- Natural-number subtraction (`n - 1`, `q - 1`, `d - 1`) is safe here since `n ≥ 1`, `q ≥ 2`,
  and `d ≥ 1` are all assumed.

No proof is attempted; the theorem ends in `:= by sorry` as instructed.
