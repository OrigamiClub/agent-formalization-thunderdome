import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  All theorems end in `:= by sorry`.

We formalize:
* the positive direction (`boolean_degree_d_is_junta`);
* the sharpness / converse direction (`sharp_below_two_d`);
* the explicit witnessing family for the converse (`sharp_witness`).
-/

open Finset

namespace FilmusIhringer

/-- The slice `binom([n],k)` : subsets of `Fin n` of cardinality exactly `k`.
(An `abbrev` so that subtype projections `.1 / .2` are available.) -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* if it agrees on the slice with the evaluation, at the
`0/1` indicator vector of the input set, of a multilinear real polynomial of total
degree `≤ d`.  Multilinearity is expressed as "each variable occurs to degree
`≤ 1`" (`MvPolynomial.degreeOf`); on the slice this is no loss of generality since
`xᵢ² = xᵢ` on `{0,1}`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The `i`-th block of `e` consecutive coordinates, `{i·e, …, i·e+e−1} ⊆ Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The explicit witnessing family.  On a `k`-set `S` the value is the number of
blocks, among the first `ℓ` blocks each of width `e`, that are entirely contained
in `S`.  As a polynomial this is `∑_{i<ℓ} ∏_{j<e} x_{i·e+j}`, which is multilinear
of total degree `e`.  When `k < 2·e` (in particular whenever `1 ≤ k < 2d` with
`e = min d k`) two disjoint blocks cannot both fit in a `k`-set, so the count is
always `0` or `1`, i.e. the function is Boolean on the slice. -/
def witnessFun (n ℓ e k : ℕ) : Slice n k → ℝ :=
  fun S => ∑ i ∈ Finset.range ℓ, if block n e i ⊆ S.1 then (1 : ℝ) else 0

/-- **Positive direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a
constant `M = m(d)` (depending only on `d`) such that: whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `M`-junta. -/
theorem boolean_degree_d_is_junta :
    ∀ d : ℕ, 1 ≤ d →
      ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-- **Converse / sharpness.**  If `1 ≤ k < 2d` then the junta bound fails: for
every `m` there exist `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)`
that is not an `m`-junta. -/
theorem sharp_below_two_d :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
        IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnesses for the converse.**  Set `e = min d k`.  For any `ℓ`
with `ℓ · e > m` and any `n` with `n ≥ 2·(ℓ·e)` and `n ≥ 2k`, the function
`witnessFun n ℓ e k` is Boolean, has degree `≤ d`, and is not an `m`-junta
(it genuinely depends on all `ℓ·e` block coordinates). -/
theorem sharp_witness :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∀ ℓ : ℕ, m < ℓ * min d k →
        ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n → 2 * k ≤ n →
          IsBoolean (witnessFun n ℓ (min d k) k) ∧
          HasDegreeLE (witnessFun n ℓ (min d k) k) d ∧
          ¬ IsJunta (witnessFun n ℓ (min d k) k) m := by
  sorry

end FilmusIhringer
