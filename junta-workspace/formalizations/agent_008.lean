/-
  Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

  STATEMENT ONLY.  Every theorem ends in `:= by sorry`; nothing is proved.

  We formalize:
    * the positive direction (k ≥ 2d  ⟹  m(d)-junta), with an explicit m : ℕ → ℕ;
    * the converse direction (1 ≤ k < 2d  ⟹  for every m a non-m-junta example);
    * the converse again, tied to the explicit witnessing family
        ∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j}),   e = min d k.

  See agent_008.md for encoding decisions and uncertainties.
-/
import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)` : subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Real `{0,1}` indicator vector of a slice element:
`1` on coordinates lying in `S`, `0` elsewhere. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- `p` is multilinear: each variable occurs with degree at most `1`. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 1

/-- A Boolean function `f` on the slice has **degree at most `d`** if it agrees, on the
whole slice, with a multilinear real polynomial of total degree `≤ d`, evaluated at the
`{0,1}` indicator vector of the subset. -/
def BooleanDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` takes only the values `0` and `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` is an **`m`-junta**: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every degree `d ≥ 1` there is a bound `m d`, depending only on `d`, such that:
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `m d`-junta. -/
theorem boolean_degree_junta_pos :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
        ∀ k : ℕ, 2 * d ≤ k →
          ∀ n : ℕ, 2 * k ≤ n →
            ∀ f : Slice n k → ℝ,
              IsBooleanValued f → BooleanDegreeLE f d → IsJunta f (m d) := by
  sorry

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then no `d`-only junta bound can hold: for every `m` there is an ambient
dimension `n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is
*not* an `m`-junta. -/
theorem boolean_degree_junta_converse :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ n : ℕ, 2 * k ≤ n ∧
            ∃ f : Slice n k → ℝ,
              IsBooleanValued f ∧ BooleanDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit witnessing family, transcribed from the informal statement.
Partition the first `ℓ · e` coordinates of `Fin n` into `ℓ` consecutive blocks of size
`e`, and take the product over blocks of the block-sums of the `{0,1}` indicator
coordinates:
`familyFun n k e ℓ (S) = ∏_{i=0}^{ℓ-1} ( Σ_{j=0}^{e-1} x_{i·e + j} )`,
where `x_t = 1` if the `t`-th coordinate lies in `S` and `0` otherwise.
Out-of-range indices contribute `0`. -/
noncomputable def familyFun (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (if (⟨i * e + j, h⟩ : Fin n) ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0)
      else 0)

/-- **Filmus–Ihringer, converse witnessed by the explicit family.**
For `1 ≤ k < 2d`, put `e = min d k`.  For every `m` one can pick a number of blocks `ℓ`
with `ℓ · e > m` and an ambient dimension `n ≥ 2k` with `n ≥ 2 · ℓ · e`, so that the
family function `∏_{i}(Σ_j x_{i·e + j})` is Boolean-valued, has Boolean degree at most
`d`, and is not an `m`-junta.  (In particular its junta size is exactly `ℓ · e`.) -/
theorem boolean_degree_junta_converse_explicit :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ ℓ n : ℕ,
            m < ℓ * min d k ∧
            2 * k ≤ n ∧
            2 * (ℓ * min d k) ≤ n ∧
            IsBooleanValued (familyFun n k (min d k) ℓ) ∧
            BooleanDegreeLE (familyFun n k (min d k) ℓ) d ∧
            ¬ IsJunta (familyFun n k (min d k) ℓ) m := by
  sorry

end FilmusIhringer
