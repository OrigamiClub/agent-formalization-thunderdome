import Mathlib

/-
Gilbert–Varshamov bound (combinatorial/existential form).

Setting: alphabet size `q ≥ 2`, block length `n ≥ 1`, target minimum Hamming
distance `d` with `1 ≤ d ≤ n`. Codewords are elements of `Fin n → Fin q`
(functions from coordinates to alphabet symbols), and `Fintype.card (Fin n → Fin q) = q ^ n`.

We use Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`), which for
`x y : ∀ i, β i` with `Fintype ι` and `DecidableEq (β i)` is defined as
`(Finset.univ.filter fun i => x i ≠ y i).card`, i.e. exactly the number of coordinates
in which `x` and `y` differ.

The hypothesis is the classical Varshamov-style sphere-packing inequality:
`M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
encoded via `Finset.range (d - 1)` (so `i` ranges over `0, ..., d - 2`, matching the
convention that an empty sum is `0` when `d = 1`).

Conclusion: there exists a code `C : Finset (Fin n → Fin q)` of exactly size `M` such
that every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent18
    (q n d : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (M : ℕ) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
