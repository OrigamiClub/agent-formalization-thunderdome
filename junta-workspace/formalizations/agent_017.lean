import Mathlib

open scoped BigOperators
open Finset

namespace Agent017

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 017).  Every theorem ends in `:= by sorry`.

We formalize:
* the forward direction (`k ≥ 2d` ⟹ uniform junta bound `m(d)`), with `m(d)`
  existentially quantified inside the statement;
* the converse direction (`1 ≤ k < 2d` ⟹ no uniform junta bound);
* the explicit witnessing family
  `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )`, `e = min d k`,
  from which the converse follows by taking `ℓ = m + 1`.
-/

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`
(identified with the coordinate set `{1,…,n}`). -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The real `0/1` indicator vector (a point of the Boolean cube) of a subset. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A slice function is Boolean if it takes only the values `0` and `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: on every point of the slice it agrees with
a real polynomial of total degree `≤ d`, evaluated at the `0/1` indicator vector.
(`MvPolynomial.totalDegree ≤ d` is the degree notion; we do not force
multilinearity, since `xᵢ² = xᵢ` on the cube makes that harmless.) -/
def HasSliceDegreeAtMost {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The `i`-th block of `e` consecutive coordinates, i.e. the elements of `Fin n`
whose value lies in `[i·e, i·e + e)`.  Block `i` (for `i = 0,…,ℓ-1`) plays the role
of the index range `{(i)e+1, …, (i)e+e}` in the paper's `1`-based notation. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t : Fin n => i * e ≤ (t : ℕ) ∧ (t : ℕ) < i * e + e)

/-- The Filmus–Ihringer witness family, as a function on the slice:
`gₗ(S) = ∏_{i=0}^{ℓ-1} ( Σ_{t ∈ block i} x_t )`, with `x` the `0/1` indicator of `S`.
This is `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )` with the `1`-based indices
translated to the blocks `block n e 0, …, block n e (ℓ-1)`. -/
def blockProduct (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i ∈ Finset.range ℓ, ∑ t ∈ block n e i, indicatorVec S.1 t

/-- **Forward direction.**  For every `d ≥ 1` there is a bound `m` (depending only
on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean function of
slice-degree `≤ d` on `binom([n],k)` is an `m`-junta. -/
theorem filmus_ihringer_forward :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanValued f → HasSliceDegreeAtMost d f → IsJunta m f := by
  sorry

/-- **Converse direction.**  If `1 ≤ k < 2d` then there is no uniform junta bound:
for every `m` there are `n ≥ 2k` and a Boolean slice-degree-`≤ d` function on
`binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanValued f ∧ HasSliceDegreeAtMost d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Explicit witnesses for the converse.**  With `e = min d k`, for every `ℓ ≥ 1`
and every `n` with `n ≥ 2k` and `n ≥ 2ℓe`, the function `blockProduct n k e ℓ` is
Boolean, has slice-degree `≤ d`, and is not an `m`-junta for any `m < ℓe`
(i.e. its junta arity is `≥ ℓe`, which is what "not `ℓe`-juntas" means here).
Instantiating `ℓ := m + 1` yields `filmus_ihringer_converse`. -/
theorem filmus_ihringer_family :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ e : ℕ, e = min d k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ n : ℕ,
        2 * k ≤ n → 2 * ℓ * e ≤ n →
          IsBooleanValued (blockProduct n k e ℓ) ∧
          HasSliceDegreeAtMost d (blockProduct n k e ℓ) ∧
          (∀ m : ℕ, m < ℓ * e → ¬ IsJunta m (blockProduct n k e ℓ)) := by
  sorry

end Agent017
