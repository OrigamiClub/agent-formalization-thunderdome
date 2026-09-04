/-
  Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

  Statement-only formalization.  Every theorem ends in `:= by sorry`.

  We state:
    * the forward direction  (`filmus_ihringer_junta`),
    * the converse in clean existential form  (`filmus_ihringer_not_junta`),
    * the explicit witnessing "flower" family  (`filmus_ihringer_flower_witness`).

  See agent_041.md for encoding decisions and uncertainties.
-/
import Mathlib

open Finset

namespace FilmusIhringer

/-- Indicator vector of `S ⊆ Fin n`, as a real point in `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` takes Boolean values `{0,1}` on the `k`-slice `binom([n],k)`. -/
def BooleanOnSlice {n : ℕ} (k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the `k`-slice: it agrees on every `k`-set with the
evaluation, at the indicator vector, of some real multivariate polynomial of
total degree `≤ d`.  (The polynomial need not be multilinear: on `{0,1}`
inputs multilinear reduction does not raise the total degree, so this matches
the usual definition.  The existential quantifier makes this the *minimum*
representing degree, which is the relevant notion on the slice.) -/
def HasSliceDegreeLE {n : ℕ} (k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Finset (Fin n), S.card = k → f S = MvPolynomial.eval (indicator S) p

/-- `f` is an `m`-junta on the `k`-slice: its value on a `k`-set `S` depends
only on `S ∩ J` for some coordinate set `J` of size `≤ m`. -/
def IsJuntaOnSlice {n : ℕ} (k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n),
      S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-! ### Forward direction -/

/-- **Filmus–Ihringer (main theorem).**  For every `d ≥ 1` there is a constant
`m d` such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d`
function on the slice `binom([n],k)` is an `m d`-junta. -/
theorem filmus_ihringer_junta :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
        ∀ k : ℕ, 2 * d ≤ k →
          ∀ n : ℕ, 2 * k ≤ n →
            ∀ f : Finset (Fin n) → ℝ,
              BooleanOnSlice k f → HasSliceDegreeLE k d f →
                IsJuntaOnSlice k (m d) f := by
  sorry

/-! ### Converse (clean existential form) -/

/-- **Filmus–Ihringer (converse).**  If `1 ≤ k < 2d`, then no single junta
bound works: for every `m` there are `n ≥ 2k` and a Boolean degree-`d`
function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_not_junta :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ n : ℕ, 2 * k ≤ n ∧
            ∃ f : Finset (Fin n) → ℝ,
              BooleanOnSlice k f ∧ HasSliceDegreeLE k d f ∧
                ¬ IsJuntaOnSlice k m f := by
  sorry

/-! ### Explicit witnessing family -/

/-- One factor of the flower function: the sum `x_{i·e} + x_{i·e+1} + ⋯ +
x_{i·e+e-1}` (0-indexed block `i` of width `e`), read off the indicator of `S`.
Out-of-range indices contribute `0` (they never occur under the size
hypothesis `2·ℓ·e ≤ n`). -/
noncomputable def flowerFactor {n : ℕ} (e i : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (if (⟨i * e + j, h⟩ : Fin n) ∈ S then (1 : ℝ) else 0)
      else 0)

/-- The flower function
`∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )` with `e = min d k`
(here `0`-indexed: blocks `i = 0,…,ℓ-1`). -/
noncomputable def flowerFn {n : ℕ} (d k ℓ : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ Finset.range ℓ, flowerFactor (min d k) i S

/-- **Explicit witnesses for the converse.**  For `1 ≤ k < 2d`, with
`e = min d k`, and for every `ℓ ≥ 1`, the flower function on any slice with
`n ≥ 2ℓe` is a Boolean degree-`d` function that is not an `ℓe`-junta.  Taking
`ℓ` with `ℓe > m` recovers `filmus_ihringer_not_junta`. -/
theorem filmus_ihringer_flower_witness :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ ℓ : ℕ, 1 ≤ ℓ →
          ∀ n : ℕ, 2 * ℓ * min d k ≤ n →
            BooleanOnSlice k (flowerFn (n := n) d k ℓ) ∧
              HasSliceDegreeLE k d (flowerFn (n := n) d k ℓ) ∧
                ¬ IsJuntaOnSlice k (ℓ * min d k) (flowerFn (n := n) d k ℓ) := by
  sorry

end FilmusIhringer
