import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 019).  Nothing is proved: every theorem ends
in `:= by sorry`.

We state:

* the positive direction `filmus_ihringer_junta_pos` (there is a bound `m(d)`);
* the negative direction `filmus_ihringer_junta_neg` with an abstract witness;
* the negative direction `filmus_ihringer_junta_neg_explicit` with the explicit
  witnessing family `hardFun` transcribed from the problem statement.
-/

open scoped BigOperators

namespace AgentO19

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`
(our stand-in for `{1, …, n}`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a slice point, as a real point of the cube. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes values `0`
and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `p` is *multilinear*: every monomial occurring in it is squarefree. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

/-- `f` has *degree `≤ d`* on the slice: it agrees, on every slice point, with
the evaluation at the indicator vector of some multilinear real polynomial of
total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such
that `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a bound `M = m(d)` (existentially quantified here, and
independent of `k` and `n`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`≤ d` function on the slice `binom([n], k)` is an `M`-junta. -/
theorem filmus_ihringer_junta_pos (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta M f := by
  sorry

/-- **Filmus–Ihringer, negative direction (abstract witness).**
If `1 ≤ k < 2d` then the junta bound fails completely: for every `m` there is an
`n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_junta_neg (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ (n : ℕ) (f : Slice n k → ℝ),
      2 * k ≤ n ∧ IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The Filmus–Ihringer hard family, transcribed from the problem statement.
With `e = min d k` and `ℓ` blocks, `hardFun n k d ℓ S` is

`∏_{i < ℓ} ( ∑_{j < e} x_{i·e + j} )`

evaluated at the indicator vector of `S` (coordinate indices `≥ n` contribute
`0`). -/
def hardFun (n k d ℓ : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i : Fin ℓ, ∑ j : Fin (min d k),
    if h : (i : ℕ) * min d k + (j : ℕ) < n then
      (if (⟨(i : ℕ) * min d k + (j : ℕ), h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0)
    else 0

/-- **Filmus–Ihringer, negative direction (explicit witness).**
For `1 ≤ k < 2d`, `e = min d k`, and any target `m`, taking enough blocks `ℓ`
(so that `ℓ·e > m`) and any `n ≥ 2·ℓ·e`, the function `hardFun` is a Boolean
degree-`≤ d` function on `binom([n], k)` that is not an `(ℓ·e)`-junta, hence
not an `m`-junta. -/
theorem filmus_ihringer_junta_neg_explicit
    (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ (ℓ n : ℕ),
      m < ℓ * min d k ∧ 2 * (ℓ * min d k) ≤ n ∧
      IsBoolean (hardFun n k d ℓ) ∧
      HasDegreeLE d (hardFun n k d ℓ) ∧
      ¬ IsJunta (ℓ * min d k) (hardFun n k d ℓ) := by
  sorry

end AgentO19
