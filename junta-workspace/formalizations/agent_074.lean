import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

Encoding summary (see `agent_074.md` for discussion):

* The slice `binom([n], k)` is modelled by the sets `S : Finset (Fin n)` with
  `S.card = k`.  A "function on the slice" is a total `f : Finset (Fin n) → ℝ`; all
  predicates below only look at `S` with `S.card = k`.
* Boolean codomain: values in `({0, 1} : Set ℝ)`.
* Degree `≤ d`: agreement on the slice with the evaluation, at the `0/1` indicator
  vector, of a multilinear `MvPolynomial (Fin n) ℝ` of `totalDegree ≤ d`.
* `m`-junta: a coordinate set `J` with `J.card ≤ m` on which the value only depends
  through `S ∩ J`.
* `m(d)` is an existential `∃ m : ℕ` under the binder `∀ d, 1 ≤ d → …`.

Three statements are given: the upper bound, the (abstract) lower bound, and the
explicit witnessing family.
-/

open Finset

namespace FilmusIhringer

variable {n : ℕ}

/-- The `0/1`-valued indicator vector in `ℝ^n` of a finite set `S ⊆ Fin n`. -/
def indicator (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` is **Boolean on the `k`-slice**: on every `k`-element set it takes a value in
`{0, 1} ⊆ ℝ`. -/
def BooleanOnSlice (k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d on the `k`-slice**: it agrees, on every `k`-element set, with
the evaluation at the `0/1` indicator vector of some *multilinear* real polynomial of
`totalDegree ≤ d`.  Multilinearity is spelled out as "every exponent occurring in the
support is `≤ 1`" (harmless on `0/1` inputs, included for faithfulness to the stated
definition). -/
def DegreeLEOnSlice (k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Finset (Fin n), S.card = k → f S = MvPolynomial.eval (indicator S) p

/-- `f` is an **`m`-junta on the `k`-slice**: there is a set `J` of at most `m`
coordinates such that the value of `f` on a `k`-element set `S` depends only on
`S ∩ J`. -/
def IsJuntaOnSlice (k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n),
      S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-- **Upper bound (Filmus–Ihringer).**
For every `d ≥ 1` there is a constant `m` (depending only on `d`) such that: for every
`k ≥ 2 d`, every `n ≥ 2 k`, and every Boolean degree-`≤ d` function on the slice
`binom([n], k)`, the function is an `m`-junta. -/
theorem boolean_degree_le_d_on_slice_is_junta :
    ∀ d : ℕ, 1 ≤ d → ∃ m : ℕ,
      ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Finset (Fin n) → ℝ,
          BooleanOnSlice k f → DegreeLEOnSlice k d f → IsJuntaOnSlice k m f := by
  sorry

/-- **Lower bound (Filmus–Ihringer), abstract form.**
If `1 ≤ k < 2 d`, then for every `m` there are some `n ≥ 2 k` and a Boolean
degree-`≤ d` function on the slice `binom([n], k)` that is *not* an `m`-junta. -/
theorem boolean_degree_le_d_on_slice_not_junta :
    ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Finset (Fin n) → ℝ,
        BooleanOnSlice k f ∧ DegreeLEOnSlice k d f ∧ ¬ IsJuntaOnSlice k m f := by
  sorry

/-! ## The explicit witnessing family

`e := min d k`, and for `0 ≤ i < ℓ` the `i`-th block is the set of coordinates
`{ i·e, i·e + 1, …, i·e + e - 1 }`.  The witness is
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)·e + j} )` (written `0`-indexed below).
Coordinates that would fall outside `Fin n` are replaced by the zero polynomial;
the hypothesis `2 * (ℓ * e) ≤ n` keeps every used coordinate in range. -/

/-- The `i`-th linear form `∑_{j=0}^{e-1} x_{i·e + j}` (out-of-range terms are `0`). -/
noncomputable def fiLinearForm (e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range e,
    if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0

/-- The product `∏_{i=0}^{ℓ-1} ( ∑_{j=0}^{e-1} x_{i·e + j} )`. -/
noncomputable def fiPoly (e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, fiLinearForm (n := n) e i

/-- The slice function attached to `fiPoly`. -/
noncomputable def fiFun (e ℓ : ℕ) : Finset (Fin n) → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (fiPoly (n := n) e ℓ)

/-- **The explicit family witnesses the lower bound.**
For `1 ≤ k < 2 d`, `e := min d k`, any `ℓ ≥ 1`, and any `n ≥ 2 · ℓ · e`, the function
`fiFun e ℓ` on the slice `binom([n], k)` is Boolean, has degree `≤ d`, and is *not* an
`ℓ · e`-junta.  Since `ℓ` is arbitrary (take `ℓ` with `ℓ · e > m`), this yields the
abstract lower bound above. -/
theorem fiFun_is_boolean_degree_le_d_and_not_junta :
    ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → k < 2 * d →
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
        BooleanOnSlice k (fiFun (n := n) (min d k) ℓ) ∧
        DegreeLEOnSlice k d (fiFun (n := n) (min d k) ℓ) ∧
        ¬ IsJuntaOnSlice k (ℓ * min d k) (fiFun (n := n) (min d k) ℓ) := by
  sorry

end FilmusIhringer
