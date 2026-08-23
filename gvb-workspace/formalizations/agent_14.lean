import Mathlib

open Finset

/-
Gilbert–Varshamov bound (combinatorial existence form).

Alphabet: `Fin q`.  Codeword: a function `Fin n → Fin q` (a length-`n` string
over the alphabet).  Two codewords `x y` "differ in at least `d`
coordinates" iff the finset of indices on which they disagree has size
`≥ d`; this is exactly the Hamming distance, written out inline via
`Finset.filter`/`Finset.card` to avoid depending on a guessed Mathlib name.

The bound: if `M` codewords of length `n` over an alphabet of size `q`
satisfy `M * (∑_{i=0}^{d-2} C(n-1,i) * (q-1)^i) < q^n`, then there exists a
code `C` (a `Finset` of codewords) with exactly `M` codewords, pairwise at
Hamming distance `≥ d`.
-/

theorem gvb_bound_agent14
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
