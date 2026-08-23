import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setting: alphabet of size `q` (encoded as `Fin q`), block length `n`
(encoded as `Fin n`), so a codeword is a function `Fin n → Fin q` and
the ambient space `Fin n → Fin q` is finite of cardinality `q ^ n`.
A code `C` is a `Finset (Fin n → Fin q)`. Two codewords `x y` have
Hamming distance `≥ d` iff the number of coordinates where they differ
is `≥ d`; this is spelled out inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `M` codewords are sought with pairwise Hamming distance
at least `d`, and `M` satisfies the Gilbert–Varshamov counting bound
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
then such a code of size exactly `M` exists.
-/

theorem gvb_bound_agent09
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
