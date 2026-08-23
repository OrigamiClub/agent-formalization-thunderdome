import Mathlib

open Finset

/-!
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet size `q`, block length `n`, minimum distance target `d`, and desired code
size `M` are all natural numbers. Codewords are modeled as functions `Fin n → Fin q`
(the `q^n`-element ambient space), and "Hamming distance at least `d`" between two
codewords `x y` is expressed directly as: the number of coordinates `i : Fin n` on
which `x i ≠ y i` is at least `d` (this is spelled out inline via `Finset.filter`
and `Finset.card` rather than via Mathlib's `hammingDist`, to avoid relying on the
exact signature/namespace of that definition).

The Gilbert–Varshamov inequality
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n
is encoded with the sum over `Finset.range (d - 1)` (using truncated natural
subtraction), since `Finset.range (d - 1) = {0, 1, ..., d-2}` has exactly `d - 1`
elements, matching the mathematical sum `∑_{i=0}^{d-2}`. When `d = 1` this range is
empty, correctly encoding the (by convention, empty) sum `∑_{i=0}^{-1}`.
-/

theorem gvb_bound_agent04
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 1 ≤ M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (Nat.choose (n - 1) i) * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
