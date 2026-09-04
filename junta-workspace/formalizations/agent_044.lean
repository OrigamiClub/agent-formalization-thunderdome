import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  All theorems end in `:= by sorry`.

We formalize:
* `filmus_ihringer_forward`   — the junta bound for `k ≥ 2d`;
* `filmus_ihringer_converse`  — failure of any uniform junta bound for `1 ≤ k < 2d`;
* `filmus_ihringer_converse_witness` — an explicit witnessing family for the converse.
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `{1, …, n}` (modeled as `Fin n`) of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a set `S ⊆ Fin n`, as a point of `Fin n → ℝ`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A Boolean function `f` on the slice `binom([n], k)` **has degree `≤ d`** if it agrees,
at every point of the slice, with the evaluation of some real polynomial of total degree
`≤ d` at the `0/1` indicator vector of the set.  (On `0/1` points a polynomial agrees with
its multilinearization, of no larger total degree, so requiring multilinearity separately
is unnecessary.) -/
def BooleanDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → Bool) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k,
        MvPolynomial.eval (indicator S.val) p = (if f S then (1 : ℝ) else 0)

/-- `f` is an **`m`-junta**: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → Bool) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a constant
`m = m(d)` (here existentially quantified) such that: whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on `binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_forward :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ,
        ∀ k : ℕ, 2 * d ≤ k →
          ∀ n : ℕ, 2 * k ≤ n →
            ∀ f : Slice n k → Bool, BooleanDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse direction.**  If `1 ≤ k < 2d` then no uniform junta bound holds: for every
`m` there is an `n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not
an `m`-junta. -/
theorem filmus_ihringer_converse :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ n : ℕ, 2 * k ≤ n ∧
            ∃ f : Slice n k → Bool, BooleanDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Explicit witnessing family for the converse.**

Put `e := min d k`.  Choose `ℓ` disjoint blocks `B i ⊆ Fin n`, each of size `e`, laid out
inside `n ≥ 2 · ℓ · e` coordinates.  The witness is
`f S = [ ∃ i, B i ⊆ S ]`, i.e. the restriction to the slice of the degree-`e` polynomial
`∑ i, ∏ j ∈ B i, X j` ("number of blocks entirely contained in `S`").

Because `k < 2·min d k`, a `k`-element set contains at most one full block, so `f` is
genuinely `{0,1}`-valued.  It has degree `≤ e ≤ d`; and for `n ≥ 2 ℓ e` it depends on all
`ℓ e` block coordinates, so once `ℓ e > m` it is not an `m`-junta. -/
theorem filmus_ihringer_converse_witness :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ ℓ n : ℕ,
            2 * k ≤ n ∧
            2 * (ℓ * min d k) ≤ n ∧
            m < ℓ * min d k ∧
            ∀ B : Fin ℓ → Finset (Fin n),
              (∀ i, (B i).card = min d k) →
              (∀ i i', i ≠ i' → Disjoint (B i) (B i')) →
                ∃ f : Slice n k → Bool,
                  (∀ S : Slice n k, f S = decide (∃ i, B i ⊆ S.val)) ∧
                  BooleanDegreeLE d f ∧
                  ¬ IsJunta m f := by
  sorry

end FilmusIhringer
