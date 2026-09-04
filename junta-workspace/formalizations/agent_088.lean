import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 088).  Every theorem ends in `:= by sorry`;
nothing is proved.

We formalize:
* the forward direction (`filmus_ihringer_slice_junta`);
* the converse / sharpness in existential form (`filmus_ihringer_slice_converse`);
* the converse together with the explicit witnessing family
  `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` (`filmus_ihringer_slice_converse_explicit`).
-/

namespace AgentO88

open scoped BigOperators

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector in `ℝ^n` of a slice element. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f : Slice n k → ℝ` has *degree at most `d`* if it agrees, at the indicator
vector of every slice point, with the evaluation of some real *multilinear*
polynomial (`degreeOf i ≤ 1` for every `i`) of total degree at most `d`. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, p.degreeOf i ≤ 1) ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = (MvPolynomial.eval (indicator S)) p

/-- `f` is an *`m`-junta*: there is a coordinate set `J` with `|J| ≤ m` such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a bound
`m` (depending only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`≤ d` function on `binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_slice_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanValued f → HasSliceDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse (sharpness), existential form.**  If `1 ≤ k < 2d` then the junta
bound fails: for every `m` there exist `n ≥ 2k` and a Boolean degree-`≤ d`
function on `binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer_slice_converse
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBooleanValued f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- Index of the `j`-th variable of the `i`-th block, embedded into `Fin n`,
given that the `ℓ` blocks of size `e` fit, i.e. `ℓ * e ≤ n`. -/
def blockIdx {n ℓ e : ℕ} (h : ℓ * e ≤ n) (i : Fin ℓ) (j : Fin e) : Fin n :=
  ⟨(i : ℕ) * e + (j : ℕ), by
    have hi : (i : ℕ) + 1 ≤ ℓ := i.2
    have hj : (j : ℕ) < e := j.2
    have step : ((i : ℕ) + 1) * e ≤ ℓ * e := mul_le_mul_right' hi e
    have expand : ((i : ℕ) + 1) * e = (i : ℕ) * e + e := by ring
    omega⟩

/-- The explicit sharpness family `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )`
as a real multilinear polynomial: the `ℓ` blocks of `e` variables each are
pairwise disjoint. -/
noncomputable def sharpPoly {n ℓ e : ℕ} (h : ℓ * e ≤ n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (blockIdx h i j)

/-- The function on `binom([n], k)` induced by `sharpPoly`. -/
noncomputable def sharpFun {n ℓ e : ℕ} (k : ℕ) (h : ℓ * e ≤ n) : Slice n k → ℝ :=
  fun S => (MvPolynomial.eval (indicator S)) (sharpPoly h)

/-- **Converse (sharpness), explicit witnessing family.**  For `1 ≤ k < 2d`,
`e = min d k`, any number of blocks `ℓ`, and `n` large enough (`n ≥ 2ℓe` and
`n ≥ 2k`), the function `sharpFun` is Boolean, has slice-degree `≤ d`, and is
not an `m`-junta for any `m < ℓ e` (all `ℓ e` coordinates are relevant).  Taking
`ℓ → ∞` this defeats any fixed junta bound. -/
theorem filmus_ihringer_slice_converse_explicit
    (d k ℓ n m : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (hnk : 2 * k ≤ n)
    (e : ℕ) (he : e = min d k)
    (hℓe : ℓ * e ≤ n) (hn : 2 * (ℓ * e) ≤ n)
    (hm : m < ℓ * e) :
    IsBooleanValued (sharpFun k hℓe) ∧
    HasSliceDegreeLE d (sharpFun k hℓe) ∧
    ¬ IsJunta m (sharpFun k hℓe) := by
  sorry

end AgentO88
