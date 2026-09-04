import Mathlib

open scoped BigOperators

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize:

* the positive direction, as an explicit bound `m : ℕ → ℕ`
  (`boolean_degree_d_on_slice_is_junta`);
* the converse, as a pure existence of a non-junta Boolean degree-`d` function
  (`boolean_degree_d_on_slice_not_junta`);
* the converse together with the explicit witnessing family
  `∏_{i<ℓ} (∑_{j<e} x_{blk i j})`, `e = min d k`
  (`boolean_degree_d_on_slice_not_junta_witnessed`).
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`. -/
def Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real `{0,1}`-valued indicator vector of a subset of `Fin n`. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the
values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ x : Slice n k, f x = 0 ∨ f x = 1

/-- `f` has *degree `≤ d`* if, on the slice, it agrees with the evaluation at the
`{0,1}` indicator vector of some real multilinear polynomial of total degree
`≤ d`.  Only the `totalDegree ≤ d` bound is imposed here; requiring the
polynomial to be multilinear would not change the notion, since it is evaluated
only at `{0,1}` points. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ x : Slice n k, f x = MvPolynomial.eval (ind x.1) p

/-- `f` is an *`m`-junta* : there is a coordinate set `J` with `|J| ≤ m` such
that the value `f x` depends only on `x ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ x y : Slice n k, x.1 ∩ J = y.1 ∩ J → f x = f y

/-- The explicit witnessing family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`.
The relabelling `(i-1)e+j ↦ blk i j` is captured abstractly by an (assumed
injective) block map `blk : Fin ℓ → Fin e → Fin n`, so that no `Fin` index
arithmetic is needed in the statement. -/
def witnessFun {n k : ℕ} (ℓ e : ℕ) (blk : Fin ℓ → Fin e → Fin n) :
    Slice n k → ℝ :=
  fun x => ∏ i : Fin ℓ, ∑ j : Fin e, ind x.1 (blk i j)

/-- **Positive direction (Filmus–Ihringer).**  There is a constant `m d` such
that whenever `d ≥ 1`, `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function
on the slice `binom([n],k)` is an `m d`-junta. -/
theorem boolean_degree_d_on_slice_is_junta :
    ∃ m : ℕ → ℕ,
      ∀ (d : ℕ), 1 ≤ d →
      ∀ (k : ℕ), 2 * d ≤ k →
      ∀ (n : ℕ), 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f (m d) := by
  sorry

/-- **Converse direction.**  If `1 ≤ k < 2d` then for every `m` there is a slice
`binom([n],k)` with `n ≥ 2k` carrying a Boolean degree-`d` function that is not
an `m`-junta. -/
theorem boolean_degree_d_on_slice_not_junta :
    ∀ (d : ℕ), 1 ≤ d →
    ∀ (k : ℕ), 1 ≤ k → k < 2 * d →
    ∀ (m : ℕ),
      ∃ (n : ℕ), 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Converse direction, with explicit witnesses.**  For `1 ≤ k < 2d` and any
`m`, set `e = min d k`.  Choosing `ℓ` large and `n ≥ 2·ℓ·e`, the function
`∏_{i<ℓ} (∑_{j<e} x_{blk i j})` on `binom([n],k)` is Boolean, has degree `≤ d`,
and is not an `ℓe`-junta (hence not an `m`-junta, since `ℓe > m`). -/
theorem boolean_degree_d_on_slice_not_junta_witnessed :
    ∀ (d : ℕ), 1 ≤ d →
    ∀ (k : ℕ), 1 ≤ k → k < 2 * d →
    ∀ (m : ℕ),
      ∃ (ℓ n : ℕ) (blk : Fin ℓ → Fin (min d k) → Fin n),
        Function.Injective (fun p : Fin ℓ × Fin (min d k) => blk p.1 p.2) ∧
        2 * k ≤ n ∧
        2 * (ℓ * min d k) ≤ n ∧
        m < ℓ * min d k ∧
        IsBoolean (witnessFun (k := k) ℓ (min d k) blk) ∧
        HasDegreeLE (witnessFun (k := k) ℓ (min d k) blk) d ∧
        ¬ IsJunta (witnessFun (k := k) ℓ (min d k) blk) (ℓ * min d k) := by
  sorry

end FilmusIhringer
