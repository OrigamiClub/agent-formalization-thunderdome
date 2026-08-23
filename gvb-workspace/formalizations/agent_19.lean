import Mathlib

/-
Gilbert–Varshamov bound (combinatorial/existential form).

Setting: alphabet of size `q` is modeled as `Fin q`, codewords of length `n`
are functions `Fin n → Fin q`, and a "code" is a `Finset` of such codewords.
The Hamming distance condition "every two distinct codewords differ in at
least `d` coordinates" is spelled out inline as a cardinality condition on
the filtered set of coordinates where the two codewords disagree.

If `M` is small enough relative to the Gilbert–Varshamov sum
  ∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i
(encoded below as `∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i`,
since `Finset.range (d - 1)` ranges over `i = 0, 1, ..., d - 2`), then there
exists a code `C` of size exactly `M` with minimum Hamming distance at
least `d`.
-/

theorem gvb_bound_agent19
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card := by
  sorry
