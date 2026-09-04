import Mathlib

open MvPolynomial

namespace Agent063

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:
* `filmus_ihringer_forward`         — the forward direction (existence of `m(d)`);
* `filmus_ihringer_converse`        — the converse, in pure existential form;
* `filmus_ihringer_converse_explicit` — the converse together with the explicit
  witnessing family `∏_i (∑_{v ∈ blockᵢ} x_v)`.
-/

/-- The slice `binom([n], k)`: subsets of `Fin n` (thought of as `{1, …, n}`) of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector in `ℝ^n` of a point `S` of the slice. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `p` is *multilinear*: every variable occurs to degree at most `1`. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

/-- `f` has *(slice-)degree at most `d`*: it agrees, on the whole slice, with the evaluation on
indicator vectors of some multilinear real polynomial of total degree at most `d`. -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the value of
`f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**  For every degree `d ≥ 1` there is a constant
`M = m(d)` (depending only on `d`) such that: whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n], k)` is an `M`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE f d → IsJunta f M := by
  sorry

/-- **Converse direction (pure form).**  If `1 ≤ k < 2d`, then for every `m` there exist
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is *not* an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Converse direction with the explicit witnessing family.**

Set `e = min d k`.  Take `ℓ` pairwise disjoint coordinate blocks `blocks 0, …, blocks (ℓ-1)`,
each of size `e` (the literal construction uses the consecutive blocks
`{(i-1)e+1, …, ie}`, but disjoint blocks of size `e` are equivalent up to a symmetry of the
slice).  The witness is the polynomial
`∏_{i} (∑_{v ∈ blocks i} X v)` — the product over the `ℓ` blocks of the block-sums.

Claim: given any `m`, one can choose `ℓ` (hence, via `n ≥ 2ℓe`, arbitrarily many essential
coordinates) so that the function this polynomial induces on `binom([n], k)` is Boolean, has
degree `≤ d`, and is not an `m`-junta. -/
theorem filmus_ihringer_converse_explicit (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ (ℓ n : ℕ) (blocks : Fin ℓ → Finset (Fin n)),
      2 * k ≤ n ∧
      2 * ℓ * min d k ≤ n ∧
      (∀ i, (blocks i).card = min d k) ∧
      (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) ∧
      ∃ f : Slice n k → ℝ,
        (∀ S : Slice n k,
          f S = eval (indicator S)
            (∏ i : Fin ℓ, ∑ v ∈ blocks i, (X v : MvPolynomial (Fin n) ℝ))) ∧
        IsBoolean f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

end Agent063
