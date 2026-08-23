import Mathlib

open Finset

/-!
Gilbert–Varshamov bound (combinatorial / existential form).

Let `q ≥ 2` be an alphabet size, `n ≥ 1` a block length, and `d` with
`1 ≤ d ≤ n` a target minimum Hamming distance. Codewords are modeled as
functions `Fin n → Fin q` (length-`n` strings over an alphabet of size
`q`). If a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} (n-1).choose i * (q-1)^i) < q^n`

then there exists a code `C`, i.e. a `Finset (Fin n → Fin q)` of size
`M`, such that every two distinct codewords in `C` have Hamming distance
at least `d`.

We spell out the Hamming-distance condition inline as
`d ≤ (univ.filter (fun i => x i ≠ y i)).card`, i.e. `x` and `y` differ
in at least `d` coordinates, rather than relying on Mathlib's
`hammingDist` (whose exact API/import path we were not fully certain
of), to keep the statement self-contained and unambiguous.
-/

theorem gvb_bound_agent12
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
