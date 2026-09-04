import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize **both directions**:

* `boolean_degree_d_is_junta`  — the positive result: for `d ≥ 1` there is a bound
  `m = m(d)` (an existential inside the statement) such that for `k ≥ 2d` and
  `n ≥ 2k` every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.
* `boolean_degree_d_not_junta` — the tightness result: for `d ≥ 1` and `1 ≤ k < 2d`,
  for every `m` there is some `n ≥ 2k` and a Boolean degree-`d` function on
  `binom([n],k)` that is not an `m`-junta.

The explicit witnessing family
`∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` is **not** encoded; the non-junta witness is
left existential.  See `agent_045.md` for the reasoning.
-/

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector in `ℝ^n` of a slice element `S`
(`1` on coordinates belonging to `S`, `0` elsewhere). -/
def sliceIndicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def BooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`*: it agrees on the whole slice with the evaluation, at the
`0/1` indicator vectors, of some multilinear real polynomial of total degree `≤ d`.
(Multilinearity — `degreeOf i p ≤ 1` for every variable `i` — is harmless on the slice,
where `x_i^2 = x_i`, but is included to match the statement literally.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S S' : Slice n k, S.1 ∩ J = S'.1 ∩ J → f S = f S'

/-- **Filmus–Ihringer, positive direction.**
Let `d ≥ 1`.  There is a constant `m(d)` (here: an existential `m : ℕ` not depending on
`k` or `n`) such that if `k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d`
function on the slice `binom([n], k)` is an `m(d)`-junta. -/
theorem boolean_degree_d_is_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, BooleanValued f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, tightness direction.**
Let `d ≥ 1`.  If `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a Boolean
degree-`d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem boolean_degree_d_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, BooleanValued f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

end FilmusIhringer
