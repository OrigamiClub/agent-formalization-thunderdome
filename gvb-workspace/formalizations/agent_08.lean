import Mathlib

open Finset

/-!
Gilbert–Varshamov bound — combinatorial / existential form.

If `q ≥ 2` is an alphabet size, `n > 0` is the code length, `d` with `1 ≤ d ≤ n` is the
desired minimum Hamming distance, and `M > 0` is a target code size satisfying

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C`, a finset of codewords of length `n` over an alphabet of size
`q` (modeled as `Fin n → Fin q`), with `|C| = M`, such that every two distinct codewords of
`C` are at Hamming distance at least `d` apart.

The alphabet is modeled by `Fin q`, which has cardinality `q` (using `2 ≤ q` to guarantee
`Fin q` is nonempty/well-behaved), and a codeword is a function `Fin n → Fin q`. Hamming
distance between two codewords `x y : Fin n → Fin q` is taken to be
`hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card`, i.e. the number of
coordinates in which they differ (`Mathlib.InformationTheory.Hamming`).
-/
theorem gvb_bound_agent08
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
