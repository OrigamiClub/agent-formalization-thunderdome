import Mathlib

/-
Gilbert–Varshamov bound (combinatorial existence form).

Setting: alphabet size `q`, block length `n`, minimum distance target `d`,
codewords modeled as functions `Fin n → Fin q`. Hamming distance between
two codewords `x y : Fin n → Fin q` is encoded inline as the cardinality
of the Finset of coordinates on which they differ.

Statement: if `M` is a positive integer with
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n
then there exists a Finset `C` of codewords with `C.card = M` such that any
two distinct codewords in `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent20
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
