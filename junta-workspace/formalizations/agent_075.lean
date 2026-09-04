import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize **both directions**:
* the forward junta bound (there is `m(d)` such that for `k ≥ 2d`, `n ≥ 2k`, every Boolean
  degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta);
* the converse (for `1 ≤ k < 2d` and every `m`, some Boolean degree-`d` function on some
  slice is not an `m`-junta),
and additionally we spell out the **explicit witnessing family**
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
-/

open scoped BigOperators

namespace FilmusIhringer

variable {n k : ℕ}

/-- The slice `binom([n],k)`: subsets of `Fin n` (a stand-in for `{1,…,n}`) of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` real indicator vector of a subset of `Fin n`. -/
noncomputable def indicator (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is **Boolean** if every value is `0` or `1`. -/
def IsBoolean (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d** on the slice: it agrees on the whole slice with the evaluation,
at `0/1` indicator vectors, of a *multilinear* real polynomial of total degree `≤ d`.
(Multilinearity `∀ i, degreeOf i p ≤ 1` matches the problem's phrasing; it is well known to
be no loss of generality on the slice.) -/
def HasDegreeLE (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, p.degreeOf i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator (S : Finset (Fin n))) p

/-- `f` is an **`m`-junta**: there is a set `J` of at most `m` coordinates such that `f S`
depends only on `S ∩ J`. -/
def IsJunta (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- One linear form `∑_{j=1}^{e} x_{i·e + j}` (0-indexed: block `i` uses coordinates
`i·e, …, i·e + e - 1`), living in `MvPolynomial (Fin n) ℝ`; out-of-range terms are `0`. -/
noncomputable def blockSum (n e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The explicit witnessing polynomial `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`. -/
noncomputable def witnessPoly (n d k ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, blockSum n (min d k) i

/-- The function on the `(n,k)`-slice induced by `witnessPoly`. -/
noncomputable def witnessFun (n d k ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator (S : Finset (Fin n))) (witnessPoly n d k ℓ)

/-- **Filmus–Ihringer** (both directions).

Forward: there is `m : ℕ → ℕ` such that for `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n],k)` is an `m d`-junta.

Converse: for `d ≥ 1` and `1 ≤ k < 2d`, for every `m` there is a slice `binom([n],k)` with
`n ≥ 2k` carrying a Boolean degree-`d` function that is not an `m`-junta. -/
theorem filmus_ihringer :
    (∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f (m d))
    ∧
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
        IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m) := by
  sorry

/-- **Explicit witnesses for the converse.**

For `d ≥ 1` and `1 ≤ k < 2d`, and any target `m`, there are `ℓ` and `n` with
`m < ℓ·e` (where `e = min d k`) and `n ≥ 2·ℓ·e` such that the function `witnessFun n d k ℓ`
induced on the `(n,k)`-slice by `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` is Boolean, has
degree `≤ d`, and is not an `m`-junta (in particular not an `ℓ·e`-junta-sized restriction
suffices). -/
theorem filmus_ihringer_converse_explicit
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ,
      m < ℓ * min d k ∧
      2 * (ℓ * min d k) ≤ n ∧
      IsBoolean (witnessFun n d k ℓ) ∧
      HasDegreeLE (witnessFun n d k ℓ) d ∧
      ¬ IsJunta (witnessFun n d k ℓ) m := by
  sorry

end FilmusIhringer
