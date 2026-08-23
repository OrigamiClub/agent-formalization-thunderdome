import Mathlib

/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup: codewords of length `n` over an alphabet of size `q` are modeled as functions
`Fin n → Fin q` (a `Fintype` of cardinality `q ^ n`). The Hamming distance between two
codewords `x y : Fin n → Fin q` is defined inline as the number of coordinates on which
they differ, `(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, and a positive integer `M` satisfies the
Gilbert–Varshamov inequality
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
then there exists a code `C`, i.e. a finite set of codewords of length `n` over the
`q`-symbol alphabet, with `|C| = M`, such that every two distinct codewords of `C` have
Hamming distance at least `d`.
-/

theorem gvb_bound_agent16
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card := by
  sorry
