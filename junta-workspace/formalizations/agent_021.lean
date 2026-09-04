import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 021).  Every theorem ends in `:= by sorry`;
nothing is proved.

We state **both directions** of the theorem together with the **explicit
witnessing family**.  See `agent_021.md` for the encoding rationale and the
uncertainties (notably a likely off-by-one in "not an `ℓ e`-junta").
-/

namespace FilmusIhringer

open scoped BigOperators

/-- The slice `binom([n], k)`, encoded as the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of `S ⊆ Fin n`, viewed as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- Evaluate a real polynomial `p` at the indicator vector of `S`. -/
noncomputable def evalAt {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  MvPolynomial.eval (indicator S) p

/-- `f` takes only the values `0` and `1`. -/
def IsBooleanValued {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- `f : Slice n k → ℝ` has degree `≤ d` if it agrees on the whole slice with a
**multilinear** real polynomial of total degree `≤ d`, evaluated at indicator
vectors.  The multilinearity clause `∀ i, p.degreeOf i ≤ 1` is kept to match the
wording of the theorem literally; on the slice it may be dropped without changing
the notion (any agreeing polynomial can be multilinearized without raising its
total degree). -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ (∀ i, p.degreeOf i ≤ 1) ∧
      ∀ S : Slice n k, f S = evalAt p S.1

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The polynomial `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e + j})`, written here with
`0`-based indices as `∏_{i < ℓ} ∑_{j < e} X_{i*e + j}`.  Indices that fall outside
`Fin n` contribute `0`; when `n ≥ 2 ℓ e` every index `i*e + j` with `i < ℓ`,
`j < e` is a genuine element of `Fin n`, so no term is lost. -/
noncomputable def blockForm (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-! ## Forward direction: `k ≥ 2d` forces a bounded junta -/

/-- **Filmus–Ihringer (junta side).**  If `d ≥ 1` then there is a constant `m(d)`
(here packaged as an existential) such that whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta. -/
theorem boolean_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ,
      ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanValued f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-! ## Converse: `1 ≤ k < 2d` allows arbitrarily non-junta functions -/

/-- **Filmus–Ihringer (sharpness side).**  If `1 ≤ k < 2d`, then for every `m`
there is a slice `binom([n],k)` with `n ≥ 2k` carrying a Boolean degree-`d`
function that is **not** an `m`-junta.  The witness is taken from the explicit
family `blockForm n (min d k) ℓ` with `ℓ` chosen large. -/
theorem not_junta_of_small_k
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ,
      2 * (ℓ * min d k) ≤ n ∧ 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          (∀ S : Slice n k, f S = evalAt (blockForm n (min d k) ℓ) S.1) ∧
            IsBooleanValued f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit family with its natural junta lower bound.  With `e = min d k`,
for every `ℓ ≥ 1` and every `n ≥ 2 ℓ e` (and `n ≥ 2k`) the function
`S ↦ blockForm n e ℓ` evaluated at `indicator S` is a Boolean degree-`d` function
on `binom([n],k)` that depends on all `ℓ e` block coordinates, hence is not an
`(ℓ e − 1)`-junta.  (The prose of the theorem phrases this as "not an
`ℓ e`-junta"; see `agent_021.md` for the off-by-one.) -/
theorem blockForm_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ)
    (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S : Slice n k, f S = evalAt (blockForm n (min d k) ℓ) S.1) ∧
        IsBooleanValued f ∧ HasDegreeLE f d ∧
        ¬ IsJunta f (ℓ * min d k - 1) := by
  sorry

end FilmusIhringer
