import Mathlib

open Finset
open scoped Classical

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Three theorems, all closed by `sorry`:

* `FilmusIhringer.forward`      — the positive direction (`k ≥ 2d` ⇒ junta);
* `FilmusIhringer.converse`     — the converse (`1 ≤ k < 2d` ⇒ no uniform junta bound);
* `FilmusIhringer.explicit_family` — explicit witnesses for the converse.

See `agent_093.md` for the encoding rationale.
-/

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` characteristic vector of a finite set, as a real point of the cube. -/
def charVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice if it agrees, at the characteristic
vector of every point of the slice, with the evaluation of some multilinear
polynomial `p ∈ ℝ[X_0, …, X_{n-1}]` of total degree at most `d`.  Multilinearity
is expressed by requiring every exponent occurring in the support of `p` to be
`≤ 1`; on the `0/1`-cube this is no loss of generality. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (charVec S.1) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that the value of `f` depends only on the intersection of the input with `J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**  For every `d ≥ 1` there is a bound
`M = m(d)` (depending only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n], k)` is an `M`-junta. -/
theorem forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-- **Filmus–Ihringer, converse direction.**  If `1 ≤ k < 2d` then the junta
bound fails: for every `m` there is some `n ≥ 2k` and a Boolean degree-`d`
function on `binom([n], k)` that is not an `m`-junta. -/
theorem converse (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnesses for the converse.**  Fix `1 ≤ k < 2d` and put
`e = min d k`.  For every `ℓ` there are `ℓ` pairwise disjoint blocks
`B 0, …, B (ℓ - 1)` of `e` coordinates each — concretely one takes the
consecutive blocks `B i = {i·e + 1, …, i·e + e}` — such that the "OR of ANDs"
function

  `f S = 1  ↔  ∃ i, B i ⊆ S`

is Boolean and has degree `≤ d` on the slice.  (The hypothesis `k < 2d` is
equivalent to `k < 2·min d k`, which guarantees that no `k`-set contains two
disjoint blocks; hence on the slice `f` coincides with the degree-`e` polynomial
`∑ i, ∏ j ∈ B i, X j`.)  Moreover `f` depends on every one of its `ℓ·e`
coordinates, so it is not an `m`-junta for any `m < ℓ·e`; letting `ℓ → ∞`
defeats every junta bound. -/
theorem explicit_family (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ ℓ : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ 2 * (ℓ * min d k) ≤ n ∧
      ∃ (B : Fin ℓ → Finset (Fin n)) (f : Slice n k → ℝ),
        (∀ i, (B i).card = min d k) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ S : Slice n k, f S = if ∃ i, B i ⊆ S.1 then (1 : ℝ) else 0) ∧
        IsBoolean f ∧ HasDegreeLE f d ∧
        (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta f m) := by
  sorry

end FilmusIhringer
