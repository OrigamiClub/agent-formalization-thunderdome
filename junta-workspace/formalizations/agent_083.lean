import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Three theorems:

* `boolean_degree_d_on_slice_is_junta` — the positive direction (`k ≥ 2d` ⇒ junta),
* `boolean_degree_d_on_slice_junta_bound_sharp` — the converse existence statement
  (`1 ≤ k < 2d` ⇒ for every `m` a non-`m`-junta degree-`d` Boolean function exists),
* `boolean_degree_d_on_slice_sharp_witness` — the explicit witnessing family.

Every theorem ends with `:= by sorry`; nothing is proved.
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`, i.e.
`{S ⊆ {1,…,n} : |S| = k}`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector in `ℝ^n` of a finite set of coordinates. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice: it agrees, at every point of the
slice, with the evaluation at the `0/1` indicator vector of some real polynomial
in `n` variables of total degree at most `d`.  (Taking the polynomial from the
full ring of `MvPolynomial (Fin n) ℝ` is the standard convention: the "degree"
of `f` is the least `d` for which such a polynomial exists.) -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
the value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Positive direction -/

/-- **Filmus–Ihringer (positive direction).**
There is a function `m : ℕ → ℕ` such that for every `d ≥ 1`, every `k ≥ 2d`, and
every `n ≥ 2k`, every Boolean degree-`d` function on the slice `binom([n],k)` is
an `m d`-junta. -/
theorem boolean_degree_d_on_slice_is_junta :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta (m d) f := by
  sorry

/-! ## Converse: sharpness of the bound `k ≥ 2d` -/

/-- **Filmus–Ihringer (converse).**
If `1 ≤ k < 2d` then the junta bound fails unboundedly: for every `m` there are
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem boolean_degree_d_on_slice_junta_bound_sharp :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
        IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## The explicit witnessing family

With `e = min d k`, split the first `ℓ·e` coordinates into `ℓ` consecutive blocks
of size `e`.  The witness polynomial is the sum over blocks of the product of the
block's variables:
`∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} X_{i·e + j}`.
(Out-of-range indices contribute `0`; under the size hypothesis `2·(ℓ·e) ≤ n` no
term ever hits that branch.)  See `agent_083.md` for the deviation from the
prompt's literal `∏_i ∑_j` shape. -/
noncomputable def witnessPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    if h : i * e + j < n then
      (MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) : MvPolynomial (Fin n) ℝ)
    else 0

/-- The witnessing function on the slice `binom([n],k)`. -/
noncomputable def witnessFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicatorVec S.1) (witnessPoly n e ℓ)

/-- **Filmus–Ihringer (explicit witnesses).**
For `1 ≤ k < 2d` and any `m`, choosing `ℓ` with `ℓ · min d k > m`, the
sum-of-products function above is, for every `n ≥ 2·(ℓ · min d k)`, a Boolean
function of degree `≤ d` on `binom([n],k)` that is not an `m`-junta. -/
theorem boolean_degree_d_on_slice_sharp_witness
    {d : ℕ} (hd : 1 ≤ d) {k : ℕ} (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
        IsBoolean (witnessFun n k (min d k) ℓ) ∧
        HasSliceDegreeLE d (witnessFun n k (min d k) ℓ) ∧
        ¬ IsJunta m (witnessFun n k (min d k) ℓ) := by
  sorry

end FilmusIhringer
