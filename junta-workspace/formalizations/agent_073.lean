/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:
  * the forward direction  (`boolean_degree_d_is_junta`): existence of a bound `m d`;
  * the converse direction  (`exists_boolean_degree_d_not_junta`): pure existence of a
    non-junta Boolean degree-`d` function when `1 ≤ k < 2d`;
  * the explicit witnessing family (`blockFun_not_junta`), transcribing the product
    `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a slice element, as an assignment `Fin n → ℝ`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun v => if v ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice: it agrees on the slice with a multilinear
real polynomial of total degree `≤ d`, evaluated at the `0/1` indicator vector.
Multilinearity is expressed as: every monomial appearing in `p` has all exponents `≤ 1`. -/
def HasDegreeLE (d : ℕ) {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ s ∈ p.support, ∀ i, s i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta (m : ℕ) {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-! ## Forward direction (Filmus–Ihringer upper bound) -/

/-- **Forward direction.**  For `d ≥ 1` there is a constant `m d` (here an existential
inside the statement) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on `binom([n], k)` is an `m d`-junta. -/
theorem boolean_degree_d_is_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ (k : ℕ), 2 * d ≤ k → ∀ (n : ℕ), 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-! ## Converse direction (tightness of `k ≥ 2d`) -/

/-- **Converse direction (existence form).**  If `1 ≤ k < 2d` then for every `m`
there is a slice `binom([n], k)` with `n ≥ 2k` carrying a Boolean degree-`d`
function that is not an `m`-junta. -/
theorem exists_boolean_degree_d_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ### Explicit witnessing family

`blockPoly e ℓ n` is the polynomial `∏_{i=0}^{ℓ-1} ( Σ_{v : i·e ≤ v < i·e + e} X v )`
in `MvPolynomial (Fin n) ℝ` (a `0`-indexed transcription of
`∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`).  When `n ≥ ℓ·e` the `i`-th factor is a sum
over the genuine `e`-element block `{i·e, …, i·e + e - 1}`, and distinct blocks are
disjoint. -/
noncomputable def blockPoly (e ℓ n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ,
    ∑ v ∈ (Finset.univ : Finset (Fin n)).filter
        (fun v : Fin n => i * e ≤ (v : ℕ) ∧ (v : ℕ) < i * e + e),
      MvPolynomial.X v

/-- The function on the slice induced by `blockPoly e ℓ n`. -/
noncomputable def blockFun (e ℓ n k : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (blockPoly e ℓ n)

/-- **Explicit witnessing family.**  With `e = min d k`, `1 ≤ k < 2d`, `ℓ ≥ 1` and
`n ≥ 2·ℓ·e`, the function induced by `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` is
Boolean, has degree `≤ d` on the slice, and is not an `ℓ·e`-junta.  Letting `ℓ → ∞`
gives, for every `m`, a Boolean degree-`d` function that is not an `m`-junta. -/
theorem blockFun_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 2 * ℓ * min d k ≤ n) :
    IsBoolean (blockFun (min d k) ℓ n k) ∧
    HasDegreeLE d (blockFun (min d k) ℓ n k) ∧
    ¬ IsJunta (ℓ * min d k) (blockFun (min d k) ℓ n k) := by
  sorry

end FilmusIhringer
