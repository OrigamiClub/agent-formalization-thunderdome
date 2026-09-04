import Mathlib

open Finset

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every `theorem` ends in `:= by sorry`.

Encoding summary (see `agent_023.md` for the reasoning):

* The slice `binom([n],k)` is `{S : Finset (Fin n) // S.card = k}`.
* A Boolean function on the slice is a real-valued `f` with every value in `{0,1}`
  (real-valued, because "degree" is defined through real polynomials).
* `f` has degree `≤ d` if it agrees on the slice with the evaluation, at the
  0/1 indicator vector, of a multilinear `MvPolynomial (Fin n) ℝ` of
  `totalDegree ≤ d`.
* `f` is an `m`-junta if some coordinate set `J` with `J.card ≤ m` determines `f`
  in the sense that `S ∩ J = T ∩ J → f S = f T`.
* `m(d)` is an existential (`∃ m : ℕ, …`).
-/

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The 0/1 real indicator vector of a finite set (used to evaluate polynomials). -/
noncomputable def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, on the slice, with the
evaluation at the 0/1 indicator vector of some multilinear real polynomial
(`degreeOf i p ≤ 1` for every variable `i`) of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (ind S.1) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that the value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## The explicit witnessing family

The problem states the witnesses as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`.
Taken literally that product is not `{0,1}`-valued on the slice (a single block
of size `e` can contain up to `e` chosen elements).  With `e = min d k` and
`1 ≤ k < 2d` one has `⌊k / e⌋ = 1`, which is exactly the condition making the
`Σ_i ∏_j` form (the *number of the first `ℓ` blocks that are fully contained in
`S`*) take values in `{0,1}`.  We therefore read the witnesses as
`Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (a Π/Σ transcription swap); see the note.
-/

/-- The polynomial `∑_{i < ℓ} ∏_{j < e} X_{i·e + j}` on `Fin n`.
Coordinates that would fall outside `Fin n` contribute a zero factor; under the
hypotheses of `witnessing_family` every index is in range. -/
noncomputable def familyPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The witnessing function on the `k`-slice:
`S ↦ ∑_{i < ℓ} ∏_{j < e} x_{i·e+j}`, i.e. the number of the first `ℓ` consecutive
`e`-blocks contained in `S`. -/
noncomputable def familyFun (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (ind S.1) (familyPoly n ℓ e)

/-! ## The theorem -/

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a
constant `m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta. -/
theorem boolean_degree_d_is_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Converse.**  If `1 ≤ k < 2d` then no single junta arity works: for every
`m` there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that
is not an `m`-junta. -/
theorem boolean_degree_d_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnesses.**  With `e = min d k` and `1 ≤ k < 2d`, the function
`familyFun n k ℓ e` on the `k`-slice of `Fin n` (for `n ≥ 2·ℓ·e`) is Boolean,
has degree `≤ d`, and genuinely depends on all `ℓ·e` of its coordinates: it is
not an `m`-junta for any `m < ℓ·e` (its minimal junta arity is exactly `ℓ·e`).
Letting `ℓ → ∞` yields the family required by `boolean_degree_d_not_junta`. -/
theorem witnessing_family (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * ℓ * min d k ≤ n) :
    IsBoolean (familyFun n k ℓ (min d k)) ∧
    HasDegreeLE (familyFun n k ℓ (min d k)) d ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (familyFun n k ℓ (min d k)) m) := by
  sorry

end FilmusIhringer
