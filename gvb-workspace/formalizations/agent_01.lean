import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet of size `q` is modelled as `Fin q`, and codewords of length `n` are
modelled as functions `Fin n → Fin q` (i.e. `(Fin q) ^ n` under the standard
Mathlib Pi-type identification). The ambient type `Fin n → Fin q` is a
`Fintype` with `Fintype.card (Fin n → Fin q) = q ^ n`, and has decidable
equality, so `Finset (Fin n → Fin q)` and the Hamming distance between two
codewords both make sense.

We use Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`),
which for `x y : Fin n → Fin q` is defined as
`(Finset.univ.filter fun i => x i ≠ y i).card`, i.e. exactly "the number of
coordinates in which `x` and `y` differ".

The Gilbert–Varshamov bound: if `M` is small enough relative to the volume
of a Hamming ball of radius `d - 1` (the sum `∑_{i=0}^{d-2} C(n-1,i) (q-1)^i`
counting, for a fixed codeword, an upper bound on the number of other
codewords that could collide with it within distance `< d`), then a code of
size `M` and minimum distance `≥ d` exists.
-/

theorem gvb_bound_agent01
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
