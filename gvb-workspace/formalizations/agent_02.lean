import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup:
- `q` is the alphabet size, `n` the block length, `d` the desired minimum
  Hamming distance, `M` a target codebook size.
- Codewords are elements of `Fin n → Fin q` (functions from coordinates to
  alphabet symbols), i.e. the ambient space `Fin q`^n.
- Hamming distance between two codewords is `hammingDist`, from
  `Mathlib.InformationTheory.Hamming`, i.e. the number of coordinates on
  which the two functions disagree.

If `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`, then there is a code
`C` (a `Finset` of codewords) of size exactly `M` in which every pair of
distinct codewords has Hamming distance at least `d`.
-/

theorem gvb_bound_agent02
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
