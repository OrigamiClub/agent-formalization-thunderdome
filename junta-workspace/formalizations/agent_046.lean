import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Formalization of the *statement* only. Both directions are stated; every theorem
ends in `:= by sorry`. See `agent_046.md` for the encoding rationale.
-/

open MvPolynomial

namespace Agent046

/-- The slice `binom([n],k) = {S ⊆ {1,…,n} : |S| = k}`, encoded as the `k`-element
subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a set `S` on the slice, as a point of `ℝ^n`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanFn {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* if it agrees on the slice with the evaluation, at the
indicator vectors, of a multilinear real polynomial of total degree `≤ d`.
Multilinearity is expressed as `degreeOf i p ≤ 1` for every variable `i`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *m-junta* if there is a set `J` of at most `m` coordinates such that
the value of `f` on `S` depends only on `S ∩ J`. -/
def IsJuntaLE {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a constant `M = m(d)` (depending on `d` only) such that
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)`
is an `M`-junta. -/
theorem filmus_ihringer_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ (k n : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanFn f → HasDegreeLE f d → IsJuntaLE f M := by
  sorry

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then no uniform junta bound holds: for every `m` there exist
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBooleanFn f ∧ HasDegreeLE f d ∧ ¬ IsJuntaLE f m := by
  sorry

/-- Literal transcription of the witnessing family displayed in the prompt,
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e + j} )` with `e = min d k`, as a polynomial in
ℕ-indexed variables (`0`-based coordinate `(i-1)e + j - 1`).  It is provided for
reference only and is deliberately *not* folded into `filmus_ihringer_not_junta`;
see `agent_046.md` for why. -/
noncomputable def FIfamily (e ℓ : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e, MvPolynomial.X (i * e + j)

end Agent046
