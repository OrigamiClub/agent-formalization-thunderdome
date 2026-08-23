import Mathlib

open Finset

/-- The Gilbert–Varshamov bound (combinatorial / existential form).

For an alphabet size `q ≥ 2`, code length `n ≥ 1`, and target minimum
Hamming distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C`, i.e. a finite set of codewords of length `n`
over an alphabet of size `q` (modeled as `Fin n → Fin q`), with `|C| = M`,
such that every two *distinct* codewords in `C` have Hamming distance at
least `d`. The Hamming distance between `x y : Fin n → Fin q` is taken
here as the number of coordinates on which they differ, encoded inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

The sum `∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i` (an empty sum, i.e. `0`, when
`d = 1`) is encoded as `∑ i ∈ Finset.range (d - 1), ...`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}` for `d ≥ 1`. -/
theorem gvb_bound_agent17
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
