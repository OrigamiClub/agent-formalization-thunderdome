/-
  Filmus–Ihringer:
  "Boolean constant-degree functions on the slice are juntas."

  STATEMENT ONLY.  Every theorem ends in `:= by sorry`; nothing is proved.

  We formalize:
    * the positive direction (`slice_boolean_degree_junta`);
    * the converse, in clean existential form (`slice_boolean_degree_not_junta`);
    * the explicit witnessing family for the converse (`witness_properties`).

  Encoding choices are documented in `agent_001.md`.
-/
import Mathlib

open Finset

namespace FilmusIhringer

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`,
    as a subtype of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Real indicator vector of a subset of `Fin n` (the point of the Boolean cube
    corresponding to a slice point). -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- `f` has *degree at most `d`* on the slice: it agrees, on every slice point,
    with the evaluation at the indicator vector of a multilinear real polynomial
    (`degreeOf i p ≤ 1` for every variable `i`) of total degree at most `d`.

    The multilinearity clause is inessential (multilinearizing on `{0,1}`-inputs
    preserves values and does not raise the total degree); it is kept to match the
    wording of the theorem. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ x : Slice n k, f x = MvPolynomial.eval (ind x.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
    `f x` depends only on `x ∩ J`.  Note `J : Finset (Fin n)` but the bound `m` is
    independent of the ambient dimension `n`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ x y : Slice n k, x.1 ∩ J = y.1 ∩ J → f x = f y

/-! ### Positive direction -/

/-- For every `d ≥ 1` there is a bound `M` (depending only on `d`) such that:
    whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
    `binom([n],k)` is an `M`-junta. -/
theorem slice_boolean_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta M f := by
  sorry

/-! ### Converse (existential form) -/

/-- If `1 ≤ k < 2d`, then for every `m` there is some `n ≥ 2k` and some Boolean
    degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem slice_boolean_degree_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ### Explicit witnessing family -/

/-- The `i`-th block: the `e` coordinates of `Fin n` whose value lies in
    `[i·e, (i+1)·e)`.  With `e = min d k` and `i < ℓ`, and `n ≥ ℓ·e`, the blocks
    `block n e 0, …, block n e (ℓ-1)` are disjoint sets of size `e`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  univ.filter (fun c : Fin n => i * e ≤ (c : ℕ) ∧ (c : ℕ) < (i + 1) * e)

/-- The Filmus–Ihringer witness on `binom([n],k)`:
    `S ↦ ∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`  with `e = min d k`,
    i.e. `S ↦ ∏_{i < ℓ} |S ∩ Bᵢ|`, where `Bᵢ` is the `i`-th block of `e`
    consecutive coordinates. -/
def witness (n k d ℓ : ℕ) (x : Slice n k) : ℝ :=
  ∏ i ∈ range ℓ, ((x.1 ∩ block n (min d k) i).card : ℝ)

/-- For `1 ≤ k < 2d`, any `ℓ`, and `n ≥ 2·ℓ·e` with `e = min d k`, the witness
    `witness n k d ℓ` is Boolean on the slice, has degree at most `d`, and is not
    an `m`-junta for any `m < ℓ·e`.  (The theorem statement records the family's
    asserted properties; taking `ℓ` large defeats any fixed junta bound.) -/
theorem witness_properties (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (witness n k d ℓ) ∧
    HasDegreeLE d (witness n k d ℓ) ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (witness n k d ℓ)) := by
  sorry

end FilmusIhringer
