import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Formalization of the *statement* only.  Every theorem ends in `:= by sorry`.

We state:
* the positive direction (`boolean_degree_junta`);
* the converse / sharpness (`boolean_degree_not_junta`);
* the explicit witnessing family (`fiFamily`, `fiFamily_witnesses`).

See `agent_031.md` for the encoding rationale and the identifiers that were guessed.
-/

open Finset

namespace FilmusIhringer

/-- The slice `binom([n],k)`, encoded as the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBooleanOn {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has (slice) degree `≤ d`: it agrees, on every point `S` of the slice, with the
evaluation at the `0/1` indicator vector of `S` of a **multilinear** real polynomial of
total degree `≤ d`.  Multilinearity is the condition that every exponent occurring in the
support of `p` is `≤ 1`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ u ∈ p.support, ∀ i, u i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an `m`-*junta*: there is a coordinate set `J` with `|J| ≤ m` such that the value
of `f` on a point `S` of the slice depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Positive direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a constant `m(d)`
(here existentially quantified) such that: whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta. -/
theorem boolean_degree_junta :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanOn f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse / sharpness.**  If `1 ≤ k < 2d` then no uniform junta bound exists: for every
`m` there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem boolean_degree_not_junta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanOn f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witnessing family.  With `e = min d k` and consecutive blocks of length
`e`, this is `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` evaluated at the `0/1` indicator vector
of `S`.  Coordinates whose index falls outside `Fin n` contribute `0`. -/
noncomputable def fiFamily (n k d ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ range ℓ, ∑ j ∈ range (min d k),
    if h : i * min d k + j < n then
      (if (⟨i * min d k + j, h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0)
    else 0

/-- The family witnesses sharpness.  Given `m`, for `ℓ` large enough that the number
`ℓ·e` of block coordinates exceeds `m`, and for `n ≥ 2ℓe`, the function `fiFamily` is a
Boolean degree-`d` function on `binom([n],k)` which is not an `m`-junta.  (The paper phrases
this as: these functions are not `ℓe`-juntas for `n ≥ 2ℓe`; since `ℓ` is unbounded and the
function genuinely depends on all `ℓe` block coordinates, its minimal junta size `ℓe` is
unbounded — which is what the `m < ℓ * min d k` / `¬ IsJunta m` form below records.) -/
theorem fiFamily_witnesses :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ ℓ n : ℕ, m < ℓ * min d k ∧ 2 * (ℓ * min d k) ≤ n ∧
        IsBooleanOn (fiFamily n k d ℓ) ∧
        HasDegreeLE d (fiFamily n k d ℓ) ∧
        ¬ IsJunta m (fiFamily n k d ℓ) := by
  sorry

end FilmusIhringer
