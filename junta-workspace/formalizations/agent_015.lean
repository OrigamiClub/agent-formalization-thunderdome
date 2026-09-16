import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization. Every theorem ends with `:= by sorry`.

We formalize:
* `filmus_ihringer_forward`          – the positive direction (existential `m(d)`);
* `filmus_ihringer_converse`         – the converse, pure existence form;
* `filmus_ihringer_converse_explicit`– the converse with the explicit witnessing family.
-/

open scoped BigOperators

namespace AgentO15

/-- The slice `binom([n],k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

variable {n k : ℕ}

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* if it agrees on the slice with the evaluation of some real
multivariate polynomial of `totalDegree ≤ d` at the `0/1` indicator vector of `S`.

(On `0/1` inputs one may always reduce to a multilinear polynomial without changing the
represented function or increasing the total degree, so we do not separately impose
multilinearity.) -/
def HasDegreeAtMost (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The Filmus–Ihringer witnessing family.

With `e` the block size and blocks `B_i = {(i-1)e+1, …, i e}` for `i = 1, …, ℓ`
(here `0`-indexed: `B_i = {i e, …, i e + e - 1}`), this is
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, i.e. the product over the `ℓ` blocks of the number
of elements of `S` lying in that block. -/
noncomputable def fiWitness (e ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ Finset.range ℓ,
    ((S.1.filter (fun a : Fin n => i * e ≤ (a : ℕ) ∧ (a : ℕ) < i * e + e)).card : ℝ)

/-- **Positive direction (Filmus–Ihringer).**
For `d ≥ 1` there is a constant `m = m(d)` such that: whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`d` function on the slice `binom([n],k)` is an `m`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeAtMost f d → IsJunta f m := by
  sorry

/-- **Converse direction (pure existence form).**
For `d ≥ 1` and `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a Boolean degree-`d`
function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeAtMost f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Converse direction with the explicit witnessing family.**
For `d ≥ 1` and `1 ≤ k < 2d`, put `e := min d k`.  For every `m` there are `ℓ` and `n` with
`n ≥ 2k`, `n ≥ 2 ℓ e` and `m ≤ ℓ e` such that `fiWitness e ℓ` is a Boolean degree-`d`
function on `binom([n],k)` which is not an `ℓ e`-junta (and hence not an `m`-junta). -/
theorem filmus_ihringer_converse_explicit (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ ℓ n : ℕ, ∃ f : Slice n k → ℝ,
      f = fiWitness (min d k) ℓ ∧
      2 * k ≤ n ∧ 2 * (ℓ * min d k) ≤ n ∧ m ≤ ℓ * min d k ∧
      IsBoolean f ∧ HasDegreeAtMost f d ∧ ¬ IsJunta f (ℓ * min d k) := by
  sorry

end AgentO15
