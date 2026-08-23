import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet: `Fin q` (a type of cardinality `q`).
Codeword space: `Fin n → Fin q`, functions from coordinates `Fin n` to the alphabet.
Hamming distance between two codewords is taken from Mathlib's `hammingDist`,
defined (for Pi types with `DecidableEq` on each fiber) as the number of
coordinates on which the two functions disagree:
  `hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card`.

Statement: if `M` is a positive integer with
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`
then there is a code `C` (a `Finset` of codewords) with `C.card = M` such that
every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent15
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
