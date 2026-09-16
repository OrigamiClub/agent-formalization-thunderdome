import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:

* `boolean_degree_junta` — the forward direction: for `d ≥ 1` there is a constant
  `m = m(d)` (existentially quantified inside the statement) such that whenever
  `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
  `m`-junta.
* `boolean_degree_not_junta` — the converse, in clean existential form: for `d ≥ 1`
  and `1 ≤ k < 2d`, for every `m` there is `n ≥ 2k` and a Boolean degree-`d`
  function on `binom([n],k)` that is not an `m`-junta.
* `boolean_degree_not_junta_explicit` — the converse again, transcribing the explicit
  witnessing family `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
  See `agent_054.md` for caveats about this transcription.
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: `k`-element subsets of `{0, 1, …, n-1}`, represented as
`k`-element `Finset ℕ` contained in `Finset.range n`. -/
abbrev Slice (n k : ℕ) : Type :=
  { S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k }

/-- The `{0,1}`-valued indicator vector (in `ℕ → ℝ`) of a point of the slice. -/
def ind {n k : ℕ} (S : Slice n k) : ℕ → ℝ :=
  fun i => if i ∈ (S : Finset ℕ) then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- A `MvPolynomial ℕ ℝ` is *multilinear* if every monomial in its support has all
exponents `≤ 1`. -/
def IsMultilinear (p : MvPolynomial ℕ ℝ) : Prop :=
  ∀ c ∈ p.support, ∀ i, c i ≤ 1

/-- `f` has *degree at most `d`* if it agrees on the slice with the evaluation, at the
indicator vector, of some multilinear real polynomial of total degree `≤ d`. -/
def HasDegreeAtMost {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧ ∀ S, f S = MvPolynomial.eval (ind S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, (S : Finset ℕ) ∩ J = (T : Finset ℕ) ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`d` function on the slice `binom([n],k)` is an `m`-junta. -/
theorem boolean_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeAtMost f d → IsJunta f m := by
  sorry

/-- **Converse direction (existential form).**
For every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, and for every `m`, there is some
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem boolean_degree_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeAtMost f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit witnessing polynomial
`∏_{i=0}^{ℓ-1} (∑_{j=0}^{e-1} x_{i·e + j})`, a `0`-indexed version of
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. -/
noncomputable def familyPoly (e ℓ : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e, MvPolynomial.X (i * e + j)

/-- The function on the slice obtained by evaluating `familyPoly e ℓ` at the indicator vector. -/
noncomputable def familyFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (ind S) (familyPoly e ℓ)

/-- **Converse direction (explicit witnesses).**
With `e = min d k`, for every `m` there are `ℓ` and `n` with `ℓ·e > m`,
`n ≥ 2k` and `n ≥ 2ℓe`, such that `familyFun n k e ℓ` is a Boolean degree-`d`
function on `binom([n],k)` that is not an `(ℓ·e)`-junta (hence not an `m`-junta).

This transcribes the family described in the source statement; see `agent_054.md`
for caveats. -/
theorem boolean_degree_not_junta_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n ℓ : ℕ,
      2 * k ≤ n ∧
      2 * (ℓ * min d k) ≤ n ∧
      m < ℓ * min d k ∧
      IsBoolean (familyFun n k (min d k) ℓ) ∧
      HasDegreeAtMost (familyFun n k (min d k) ℓ) d ∧
      ¬ IsJunta (familyFun n k (min d k) ℓ) (ℓ * min d k) := by
  sorry

end FilmusIhringer
