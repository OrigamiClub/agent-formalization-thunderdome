import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (all theorems end in `sorry`).

We formalize three statements:

* `filmus_ihringer_forward`   — the junta upper bound for `k ≥ 2d`;
* `filmus_ihringer_converse`  — the failure of the junta property for `1 ≤ k < 2d`;
* `filmus_ihringer_witness`   — the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
-/

namespace FilmusIhringer

open scoped BigOperators

/-- The slice `binom([n], k)` : subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- Real `0/1` indicator vector of a subset of `Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A function on the slice is Boolean if all its values lie in `{0,1} ⊆ ℝ`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- A function on the slice has **degree `≤ d`** if it agrees, on the whole slice, with the
evaluation at the `0/1` indicator vector of some *multilinear* real polynomial of
total degree `≤ d`.  (On the slice, restricting to multilinear representatives is
without loss of generality, since `x_i^2 = x_i` on `{0,1}^n`.) -/
def BooleanDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- A function on the slice is an **`m`-junta** if there is a set `J` of at most `m`
coordinates such that the value on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Forward direction: `k ≥ 2d` ⟹ constant-degree Boolean functions are juntas -/

/-- **Filmus–Ihringer (upper bound).**  For every `d ≥ 1` there is a bound `m(d)` such
that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `m(d)`-junta. -/
theorem filmus_ihringer_forward :
    ∃ M : ℕ → ℕ, ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
      ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → BooleanDegreeLE d f →
        IsJunta (M d) f := by
  sorry

/-! ## Converse: `1 ≤ k < 2d` ⟹ the junta bound fails -/

/-- **Filmus–Ihringer (lower bound).**  If `d ≥ 1` and `1 ≤ k < 2d`, then for every `m`
there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_converse :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ BooleanDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## The explicit witnessing family -/

/-- The Filmus–Ihringer witnessing family.  With `e := min d k` and `ℓ` blocks, the
`i`-th block (`0 ≤ i < ℓ`) is the set of coordinates `c` with `(c : ℕ) / e = i`, i.e.
`{ i·e, i·e+1, …, i·e+e-1 }`.  The function is
`f(S) = ∏_{i=0}^{ℓ-1} |S ∩ Bᵢ|`, which is exactly
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` evaluated at the indicator vector of `S`. -/
def witnessFun (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ Finset.range ℓ, ((S.1.filter (fun c : Fin n => (c : ℕ) / e = i)).card : ℝ)

/-- **Filmus–Ihringer (explicit family).**  For `d ≥ 1`, `1 ≤ k < 2d`, any number of
blocks `ℓ ≥ 1`, and any `n ≥ 2·ℓ·e` with `e = min d k`, the function `witnessFun` is
Boolean, has degree `≤ d` on the slice, and is not an `m`-junta for any `m < ℓ·e`
(so its junta number is exactly `ℓ·e`, which is unbounded as `ℓ → ∞`). -/
theorem filmus_ihringer_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (witnessFun n k (min d k) ℓ) ∧
    BooleanDegreeLE d (witnessFun n k (min d k) ℓ) ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (witnessFun n k (min d k) ℓ)) := by
  sorry

end FilmusIhringer
