import Mathlib

/-!
# Gilbert–Varshamov bound (combinatorial/existential form)

For alphabet size `q ≥ 2`, block length `n ≥ 1`, and desired minimum Hamming
distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`

then there exists a code `C`, i.e. a `Finset` of codewords (functions
`Fin n → Fin q`, thought of as length-`n` strings over an alphabet of size
`q`), with `|C| = M`, such that every two *distinct* codewords of `C` have
Hamming distance (the number of coordinates in which they differ) at least
`d`.

The Hamming distance between `x y : Fin n → Fin q` is encoded inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the cardinality of the
set of coordinates on which `x` and `y` disagree; this avoids relying on a
specific Mathlib `Hamming` API name that we were not fully certain of.

The sum `∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i` is encoded as
`∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}` for `d ≥ 1` (and is empty when
`d = 1`, matching the convention that the sum is empty / `0` in that edge
case, forcing `M < q^n`, which is the correct GV statement for `d = 1`).
-/

theorem gvb_bound_agent10
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
