/-
  Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

  STATEMENT ONLY.  Every theorem ends in `:= by sorry`; nothing is proved.

  We state:
    * `boolean_degree_le_junta_of_k_ge_two_d`
        — the forward direction (k ≥ 2d  ⇒  m(d)-junta), with m(d) as an
          existential `∃ m : ℕ` inside the statement;
    * `exists_boolean_degree_le_not_junta_of_k_lt_two_d`
        — the converse (1 ≤ k < 2d  ⇒  for every m a Boolean degree-d
          non-m-junta exists), plain existential form;
    * `explicit_witness_not_junta_of_k_lt_two_d`
        — the converse again, this time *exhibiting* the explicit family
          ∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j}),  e = min d k.

  See `agent_005.md` for the encoding rationale and the identifiers I am
  least sure about.
-/
import Mathlib

open Finset

namespace FilmusIhringerJunta

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of `S`, viewed as a point of `ℝ^n`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then 1 else 0

/-- A real-valued function on the slice is *Boolean* if all of its values lie in `{0,1}`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice if it agrees, at every point of the
slice, with the evaluation at the indicator vector of some **multilinear** real
polynomial (each variable degree `≤ 1`) of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta* if there is a coordinate set `J` with `|J| ≤ m` such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-! ### Forward direction (k ≥ 2d) -/

/-- **Filmus–Ihringer, forward direction.**
For `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta. -/
theorem boolean_degree_le_junta_of_k_ge_two_d (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-! ### Converse direction (1 ≤ k < 2d), plain form -/

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then for every `m` there is some `n ≥ 2k` and a Boolean
degree-`d` function on `binom([n],k)` that is *not* an `m`-junta. -/
theorem exists_boolean_degree_le_not_junta_of_k_lt_two_d
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk' : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ### Converse direction, explicit witnessing family -/

/-- The explicit witnessing polynomial

  `∏_{i < ℓ} ( ∑_{j < e} X_{emb (i,j)} )`,

where `emb (i,j)` is the coordinate `(i-1)·e + j` of the original statement,
here 0-indexed as `i·e + j` (pinned down in the theorem below). -/
noncomputable def witnessPoly {n : ℕ} (emb : ℕ × ℕ → Fin n) (ℓ e : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ range ℓ, ∑ j ∈ range e, MvPolynomial.X (emb (i, j))

/-- **Filmus–Ihringer, converse direction, explicit family.**
For `1 ≤ k < 2d` and every `m`, with `e := min d k`, there is a number of blocks
`ℓ` (with `ℓ·e > m`), an ambient size `n ≥ 2k` with `n ≥ 2·ℓ·e`, and a coordinate
placement `emb` realising the pattern `(i-1)e + j` (0-indexed: `i·e + j`), such
that the slice function induced by `witnessPoly emb ℓ e` is Boolean, has
degree `≤ d`, and is not an `m`-junta.

(The paper phrases the last point as "not an `ℓe`-junta"; taken literally with the
set `J` of all `ℓe` used coordinates that is false, so we read it as *essentially
depending on all `ℓe` coordinates*, i.e. not an `m`-junta for any `m < ℓe`.) -/
theorem explicit_witness_not_junta_of_k_lt_two_d
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk' : k < 2 * d) (m : ℕ) :
    ∃ (ℓ n : ℕ) (emb : ℕ × ℕ → Fin n),
      2 * k ≤ n ∧
      2 * (ℓ * min d k) ≤ n ∧
      m < ℓ * min d k ∧
      (∀ i j, i < ℓ → j < min d k → (emb (i, j)).val = i * min d k + j) ∧
      IsBoolean (fun S : Slice n k =>
        MvPolynomial.eval (indicator S) (witnessPoly emb ℓ (min d k))) ∧
      HasDegreeLE d (fun S : Slice n k =>
        MvPolynomial.eval (indicator S) (witnessPoly emb ℓ (min d k))) ∧
      ¬ IsJunta m (fun S : Slice n k =>
        MvPolynomial.eval (indicator S) (witnessPoly emb ℓ (min d k))) := by
  sorry

end FilmusIhringerJunta
