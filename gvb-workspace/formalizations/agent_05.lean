import Mathlib

open Finset

/-- **The Gilbert–Varshamov bound** (combinatorial / existential form).

Let `q ≥ 2` be an alphabet size, `n ≥ 1` a block length, and `d` a desired
minimum Hamming distance with `1 ≤ d ≤ n`. A codeword is a function
`Fin n → Fin q` (a length-`n` string over an alphabet of size `q`), and the
Hamming distance between two codewords is the number of coordinates on which
they differ (`hammingDist`, from `Mathlib.InformationTheory.Hamming`).

If a positive integer `M` satisfies
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`
(the sum ranges over `i ∈ Finset.range (d - 1)`, i.e. `i = 0, …, d - 2`; it
is the empty sum, hence `0`, when `d = 1`), then there exists a code
`C ⊆ (Fin n → Fin q)` (a `Finset` of codewords) with `C.card = M` such that
every two *distinct* codewords of `C` are at Hamming distance at least `d`
from one another. -/
theorem gvb_bound_agent05
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
