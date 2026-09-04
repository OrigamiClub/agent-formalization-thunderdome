import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement only.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize all three pieces:

* **(I)**  the positive direction: for `k ≥ 2d` every Boolean degree-`d` function on the
  slice `binom([n],k)` is an `m(d)`-junta, with `m : ℕ → ℕ` an explicit (here: existentially
  quantified) function of `d` only;
* **(II)** sharpness: for `1 ≤ k < 2d` there is *no* junta bound whatsoever;
* **(III)** the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
-/

/-- The slice `binom([n], k)`, realized as the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real `0/1` indicator vector of a finite set of coordinates. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` is Boolean on the slice: it takes only the values `0` and `1`. -/
def IsBooleanOnSlice {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has **degree `≤ d`** on the slice: it agrees on the slice with the evaluation,
at `0/1` indicator vectors, of a *multilinear* real polynomial of total degree `≤ d`.
Multilinearity is encoded as "each variable occurs to degree `≤ 1`". -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S.1) p

/-- `f` is an **`m`-junta**: there is a set `J` of at most `m` coordinates such that the
value of `f` on the slice depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit Filmus–Ihringer family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, read on the `k`-slice of `Fin n`.

Here block `i` (for `i < ℓ`) is the set of coordinates `{i*e, i*e+1, …, i*e+e-1}`, and the
`i`-th factor `∑_{j} x_{…}` evaluated at the indicator vector of `S` is exactly the number of
elements of `S` lying in block `i`. -/
def flowerFun (n k d ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ Finset.range ℓ,
    ((S.1.filter (fun c : Fin n =>
        i * min d k ≤ (c : ℕ) ∧ (c : ℕ) < i * min d k + min d k)).card : ℝ)

/-- **Filmus–Ihringer.**  Boolean constant-degree functions on the slice are juntas, and
this is sharp exactly at `k = 2d`. -/
theorem filmus_ihringer :
    -- (I)  Positive direction: a `d`-only junta bound for `k ≥ 2d`.
    (∃ m : ℕ → ℕ,
        ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
          ∀ f : Slice n k → ℝ,
            IsBooleanOnSlice f → HasDegreeLE f d → IsJunta f (m d))
    ∧
    -- (II)  Sharpness: for `1 ≤ k < 2d` no junta bound exists at all — for every `M`
    -- there is a slice and a Boolean degree-`d` function on it that is not an `M`-junta.
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ M : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
          IsBooleanOnSlice f ∧ HasDegreeLE f d ∧ ¬ IsJunta f M)
    ∧
    -- (III)  The explicit witnessing family (`e = min d k`, `ℓ` blocks, `1 ≤ ℓ ≤ e`):
    -- it is Boolean, has degree `≤ d`, and genuinely depends on all `ℓ·e` of its
    -- coordinates, i.e. it is not an `M`-junta for any `M < ℓ·e`.
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ min d k →
        ∀ n : ℕ, 2 * k ≤ n → 2 * (ℓ * min d k) ≤ n →
          IsBooleanOnSlice (flowerFun n k d ℓ) ∧
          HasDegreeLE (flowerFun n k d ℓ) d ∧
          (∀ M : ℕ, M < ℓ * min d k → ¬ IsJunta (flowerFun n k d ℓ) M)) := by
  sorry

end FilmusIhringer
