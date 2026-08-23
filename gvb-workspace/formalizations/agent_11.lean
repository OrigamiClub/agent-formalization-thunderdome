import Mathlib

/-!
# Gilbert–Varshamov bound (combinatorial / existential form)

For alphabet size `q ≥ 2`, block length `n ≥ 1`, and target minimum Hamming
distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C ⊆ (Fin n → Fin q)` (thought of as the set of
length-`n` strings over a `q`-ary alphabet) with `|C| = M`, such that every
two distinct codewords of `C` have Hamming distance at least `d`, where the
Hamming distance between `x y : Fin n → Fin q` is encoded inline as the
number of coordinates `i : Fin n` on which `x i ≠ y i`.

Encoding notes:
* The alphabet `Fin q` and ambient space `Fin n → Fin q` are the standard
  Mathlib-style encodings of "q-ary strings of length n"; `Fintype.card
  (Fin n → Fin q) = q ^ n` matches the right-hand side of the hypothesis.
* The sum `∑_{i=0}^{d-2} C(n-1,i) (q-1)^i` (the size of a Hamming ball of
  radius `d-2` around a fixed point in the "one fewer coordinate" space,
  as used in the classical greedy/counting proof of GVB) is written as
  `∑ i in Finset.range (d - 1), (n-1).choose i * (q-1)^i` using truncated
  natural-number subtraction; `Finset.range (d - 1) = {0, ..., d-2}`, and
  when `d = 1` this range is empty, so the sum correctly degenerates to `0`.
* Hamming distance itself is not looked up as a named Mathlib definition;
  it is spelled out directly via `Finset.filter` on `Finset.univ : Finset (Fin n)`
  to avoid guessing at an unfamiliar identifier (Mathlib does have a
  `Hamming` type synonym with a `hammingDist` function, which would be an
  equally faithful alternative encoding).
-/

theorem gvb_bound_agent11
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
