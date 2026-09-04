import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.
See `agent_025.md` for the encoding notes and caveats.
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Characteristic (indicator) vector of a finite set, as a real point of the cube
`{0,1}^n ⊆ ℝ^n`. -/
def charVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f : Slice n k → ℝ` *has degree `≤ d`* if it agrees, at every point of the slice, with the
evaluation at the characteristic vector of some **multilinear** real polynomial
(`degreeOf i ≤ 1` for every variable `i`) of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, p.degreeOf i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, MvPolynomial.eval (charVec S.1) p = f S

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the value of
`f` on a slice element `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Positive direction -/

/-- **Filmus–Ihringer, junta theorem.**
For every degree `d ≥ 1` there is a bound `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`≤ d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem boolean_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-! ## Negative direction (sharpness of the range `k ≥ 2d`) -/

/-- **Sharpness.**  If `1 ≤ k < 2d` then no uniform junta bound exists: for every `m` there are
`n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem boolean_degree_not_junta (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ## Explicit witnessing family -/

/-- The witnessing polynomial `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e + j} )` with `e = min d k`,
written with `0`-based indices `i ∈ {0,…,ℓ-1}`, `j ∈ {0,…,e-1}` and coordinate `i*e + j`.
Coordinates that are out of range (which never occurs once `ℓ * min d k ≤ n`) contribute `0`. -/
noncomputable def familyPoly (n d k ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (min d k),
    (if h : i * min d k + j < n then MvPolynomial.X (⟨i * min d k + j, h⟩ : Fin n) else 0)

/-- The slice function attached to `familyPoly`. -/
noncomputable def familyFun (n d k ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (charVec S.1) (familyPoly n d k ℓ)

/-- **The explicit family witnesses the negative direction.**
Assume `1 ≤ k < 2d` and set `e = min d k`.  For every `ℓ` and every `n` with `n ≥ 2k` and
`n ≥ 2ℓe`, the function `familyFun n d k ℓ` is Boolean, has degree `≤ d` on the slice, and is
*not* an `m`-junta for any `m < ℓe` (i.e. it genuinely depends on all `ℓe` coordinates
`x_1, …, x_{ℓe}`). -/
theorem familyFun_witness (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * k ≤ n) (hn' : 2 * ℓ * min d k ≤ n) :
    IsBoolean (familyFun n d k ℓ) ∧
    HasDegreeLE (familyFun n d k ℓ) d ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (familyFun n d k ℓ) m) := by
  sorry

end FilmusIhringer
