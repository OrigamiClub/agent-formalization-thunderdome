import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup: an alphabet of size `q` is modeled as `Fin q`, and a codeword of length `n`
is modeled as a function `Fin n → Fin q`. Two codewords `x y : Fin n → Fin q` have
Hamming distance `≥ d` exactly when they differ in at least `d` of the `n`
coordinates, which we spell out inline as
`d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`.

The hypothesis is the classical Gilbert–Varshamov inequality
`M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
encoded via `Finset.range (d - 1)` (which enumerates `i = 0, …, d-2`).

The conclusion asserts the existence of a code `C`, i.e. a finite set of
codewords of length `n` over the `q`-ary alphabet, with exactly `M` codewords,
such that every two *distinct* codewords of `C` have Hamming distance at
least `d`.
-/

theorem gvb_bound_agent13
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
