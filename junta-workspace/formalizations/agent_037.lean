/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization.  Nothing here is proved: every theorem ends in `sorry`.

We state:
  * the positive direction  (k ≥ 2d  ⇒  Boolean degree-d functions are m(d)-juntas),
  * the negative direction  (1 ≤ k < 2d  ⇒  no uniform junta bound), and
  * the explicit witnessing family  ∏_{i}(∑_{j} x_{ie+j}).
-/
import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-! ## Basic objects -/

/-- The slice `binom([n],k)` : the `k`-element subsets of `{1,…,n}` (modelled on `Fin n`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real `0/1` indicator vector of a slice point. -/
def sliceIndicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if all of its values lie in `{0,1}`. -/
def IsBooleanFn {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* on the slice: it agrees, at every slice point, with the evaluation
at the `0/1` indicator vector of some multilinear real polynomial (each variable of degree
`≤ 1`) of total degree `≤ d`. -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the value
of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      ((S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J) → f S = f T

/-! ## Main theorem (both directions) -/

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

* Positive direction: there is a bound `m` (depending on `d`) such that whenever `k ≥ 2d`
  and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.

* Negative direction: whenever `1 ≤ k < 2d`, there is no such uniform bound — for every `m`
  there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
  `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ, ∀ (k n : ℕ) (f : Slice n k → ℝ),
        2 * d ≤ k → 2 * k ≤ n →
        IsBooleanFn f → HasSliceDegreeLE f d → IsJunta m f)
  ∧
    (∀ (k : ℕ), 1 ≤ k → k < 2 * d → ∀ (m : ℕ),
        ∃ (n : ℕ) (f : Slice n k → ℝ),
          2 * k ≤ n ∧ IsBooleanFn f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta m f) := by
  sorry

/-! ## The explicit witnessing family -/

/-- The `i`-th block linear form `∑_{j=1}^{e} x_{i·e + j}` (0-based: variables `i*e , … , i*e+e-1`),
with out-of-range indices contributing `0`. -/
noncomputable def blockLinear (n e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The witness polynomial `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e + j})`. -/
noncomputable def witnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, blockLinear n e i

/-- The function induced on the slice by `witnessPoly` (evaluation at the `0/1` indicator). -/
noncomputable def witnessFn (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (sliceIndicator S) (witnessPoly n ℓ e)

/-- **Explicit lower-bound family.**  For `1 ≤ k < 2d`, put `e = min d k`.  For every `ℓ ≥ 1`
and every `n` with `n ≥ 2k` and `n ≥ 2ℓe`, the function `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`
is a Boolean degree-`d` function on `binom([n],k)` whose minimal junta support has size exactly
`ℓe`: it is an `ℓe`-junta but not an `(ℓe−1)`-junta.  Letting `ℓ → ∞` beats every fixed `m`. -/
theorem filmus_ihringer_witness
    (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (e : ℕ) (he : e = min d k)
    (n : ℕ) (hn1 : 2 * k ≤ n) (hn2 : 2 * ℓ * e ≤ n) :
    IsBooleanFn (witnessFn n k ℓ e) ∧
    HasSliceDegreeLE (witnessFn n k ℓ e) d ∧
    IsJunta (ℓ * e) (witnessFn n k ℓ e) ∧
    ¬ IsJunta (ℓ * e - 1) (witnessFn n k ℓ e) := by
  sorry

end FilmusIhringer
