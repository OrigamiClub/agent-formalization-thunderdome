import Mathlib

/-
Gilbert–Varshamov bound (combinatorial/existential form).

Alphabet: `Fin q`, codeword length `n`, so the ambient space of all words is
`Fin n → Fin q`, which has cardinality `q ^ n`.

Hamming distance between two words is taken to be Mathlib's `hammingDist`
(from `Mathlib.InformationTheory.Hamming`), i.e. the number of coordinates
on which the two functions disagree.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, `M ≥ 1`, and

    M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n

(encoded below as `∑ i in Finset.range (d - 1), ...`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}`), then there is a code
`C : Finset (Fin n → Fin q)` of size exactly `M` all of whose distinct
pairs of codewords are at Hamming distance at least `d`.
-/

theorem gvb_bound_agent03
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
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
