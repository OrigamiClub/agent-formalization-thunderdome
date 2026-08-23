import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet of size `q` is modeled as `Fin q`, and codewords of length `n` over
this alphabet as functions `Fin n → Fin q`. The Hamming distance between two
codewords is the number of coordinates on which they differ; we use
Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`) for this,
which is defined (up to the `Hamming` type-synonym wrapper) as
`(Finset.univ.filter fun i => x i ≠ y i).card`. If `hammingDist` turns out
not to be the exact identifier/API in the Mathlib version being used, the
same quantity can be written inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, and a positive integer `M`
satisfies
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n,
then there is a code `C` (a `Finset` of codewords) with `C.card = M` such
that every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent06
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
