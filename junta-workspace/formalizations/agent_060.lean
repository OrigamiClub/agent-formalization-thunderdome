import Mathlib

open scoped BigOperators
open MvPolynomial

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization. Every theorem ends in `:= by sorry`; nothing is proved.

We formalize three statements:

* `boolean_degree_d_is_junta` — the forward direction, with the junta bound `m d`
  packaged as an existential `∃ m : ℕ → ℕ` inside the statement.
* `sharp_threshold_converse` — the converse in abstract "for every `m` there is a
  non-`m`-junta" form.
* `sharp_threshold_converse_explicit` — the converse together with the explicit
  witnessing family.

See `agent_060.md` for the encoding rationale (in particular a deliberate reading
of the witnessing family as a sum of products rather than a product of sums).
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)`: subsets of `Fin n` of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator point of a slice element, as an input for a real polynomial. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ := fun i => if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is *Boolean* if all its values are `0` or `1`. -/
def IsBooleanFn {n k : ℕ} (f : Slice n k → ℝ) : Prop := ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* if it agrees on the slice with the evaluation, at `0/1`
indicator points, of some real polynomial of total degree `≤ d`.  (Multilinearity is
not imposed: on the slice any polynomial can be multilinearized, and the existential
makes this harmless.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = eval (indicator S) p

/-- `f` is an *`m`-junta* if some set `J` of at most `m` coordinates determines it:
whenever two slice elements have the same intersection with `J`, `f` agrees on them. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**  For every degree bound `d ≥ 1` there is
a junta bound `m d` such that on every wide enough slice (`k ≥ 2d` and `n ≥ 2k`) every
Boolean degree-`d` function is an `m d`-junta.  The bound is an existential
`m : ℕ → ℕ` inside the statement. -/
theorem boolean_degree_d_is_junta :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
      ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanFn f → HasDegreeLE f d → IsJunta f (m d) := by
  sorry

/-- **Converse direction, abstract form.**  When `1 ≤ k < 2d` no single junta bound
works: for every `m` there is a slice `binom([n],k)` with `n ≥ 2k` carrying a Boolean
degree-`d` function that is not an `m`-junta. -/
theorem sharp_threshold_converse :
    ∀ d : ℕ, 1 ≤ d →
    ∀ k : ℕ, 1 ≤ k → k < 2 * d →
    ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
        IsBooleanFn f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The `i`-th block of `e` consecutive coordinates, `{i·e, …, i·e + e − 1} ⊆ Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c : Fin n => i * e ≤ (c : ℕ) ∧ (c : ℕ) < i * e + e

/-- Explicit witnessing polynomial: an "OR of `ℓ` disjoint size-`e` ANDs",
`∑_{i=0}^{ℓ-1} ∏_{c ∈ block i} X c`, with `e = min d k`.  Its total degree is `e ≤ d`,
*independently of `ℓ`*. -/
noncomputable def fiPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ c ∈ block n e i, MvPolynomial.X c

/-- The explicit witness on `binom([n],k)`: `fiPoly` evaluated at indicators.  On the
slice it computes `#{ i < ℓ : block i ⊆ S }`, which lies in `{0,1}` because `k < 2d`
forces `2·min(d,k) > k`, so at most one block fits inside an `S` of size `k`. -/
noncomputable def fiWitness (n k d ℓ : ℕ) : Slice n k → ℝ :=
  fun S => eval (indicator S) (fiPoly n (min d k) ℓ)

/-- **Converse direction, explicit family.**  For `1 ≤ k < 2d` put `e = min d k`.  For
every `ℓ` and every `n` with `n ≥ 2k` and `n ≥ 2ℓe`, `fiWitness n k d ℓ` is a Boolean
degree-`d` function on `binom([n],k)` that essentially depends on all `ℓe` block
coordinates; hence it is not an `m`-junta for any `m < ℓe`.  Letting `ℓ → ∞` defeats
every junta bound. -/
theorem sharp_threshold_converse_explicit :
    ∀ d : ℕ, 1 ≤ d →
    ∀ k : ℕ, 1 ≤ k → k < 2 * d →
    ∀ ℓ : ℕ, ∀ n : ℕ, 2 * k ≤ n → 2 * ℓ * min d k ≤ n →
      IsBooleanFn (fiWitness n k d ℓ) ∧
      HasDegreeLE (fiWitness n k d ℓ) d ∧
      ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (fiWitness n k d ℓ) m := by
  sorry

end FilmusIhringer
