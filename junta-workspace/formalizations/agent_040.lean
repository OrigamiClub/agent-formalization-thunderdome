import Mathlib

open scoped BigOperators

namespace Agent040

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:

* `filmus_ihringer` — both directions as one theorem: the existential constant
  `m(d)`, the junta upper bound for `k ≥ 2d`, and the sharpness (non-junta
  functions exist) for `1 ≤ k < 2d`.

* `filmus_ihringer_explicit_family` — the explicit witnessing family
  `∏_{i<ℓ} (∑_{j<e} x_{ι(i,j)})`, `e = min d k`, for the lower bound.
-/

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`
(used as a stand-in for `{1, …, n}`). -/
def Slice (n k : ℕ) : Type :=
  {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of `S ⊆ Fin n`, as a real point of the cube. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f : Slice n k → ℝ` has *degree ≤ d* if it agrees, at every point of the slice,
with the evaluation at the indicator vector of some real multilinear polynomial of
total degree `≤ d`.

Dropping the multilinearity clause `∀ i, p.degreeOf i ≤ 1` yields an equivalent
notion, since `x_i ^ 2 = x_i` on `0/1` inputs; it is kept here to match the
theorem statement literally. -/
def DegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ (∀ i, p.degreeOf i ≤ 1) ∧
    ∀ S : Slice n k, MvPolynomial.eval (indicator S.val) p = f S

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- Restriction of a real polynomial to the slice (evaluation at indicator vectors). -/
noncomputable def restrict {n k : ℕ} (p : MvPolynomial (Fin n) ℝ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S.val) p

/-- The Filmus–Ihringer witness polynomial
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, with the `ℓ · e` block variables placed
into `Fin n` by an indexing `ι` (taken to be injective in the theorem below).

Using an arbitrary injection instead of the concrete consecutive blocks
`x_{(i-1)e+j}` is harmless for the statement: only pairwise disjointness of the
`ℓ` blocks of `e` distinct variables is mathematically relevant. -/
noncomputable def witnessPoly {n : ℕ} (e ℓ : ℕ) (ι : Fin ℓ × Fin e → Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (ι (i, j))

/-- **Filmus–Ihringer** (statement only; both directions).

For every `d ≥ 1` there is a constant `m = m(d)` such that:

* (Junta / upper bound) whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d`
  function on the slice `binom([n], k)` is an `m`-junta;

* (Sharpness / lower bound) whenever `1 ≤ k < 2d`, for every `m'` there exist
  `n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not an
  `m'`-junta. -/
theorem filmus_ihringer :
    ∀ d : ℕ, 1 ≤ d → ∃ m : ℕ,
      (∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → DegreeLE d f → IsJunta m f) ∧
      (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m' : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Slice n k → ℝ, IsBoolean f ∧ DegreeLE d f ∧ ¬ IsJunta m' f) := by
  sorry

/-- **Filmus–Ihringer**, explicit witnessing family for the lower bound.

Let `1 ≤ k < 2d` and put `e = min d k`.  For any target `m` there are `ℓ` and
`n ≥ 2 · ℓ · e` and an injective placement `ι` of the `ℓ · e` block variables into
`Fin n` such that the restriction to the slice `binom([n], k)` of
`∏_{i<ℓ} (∑_{j<e} x_{ι(i,j)})` is a Boolean function of degree `≤ d` that is not an
`(ℓ · e)`-junta; moreover `ℓ · e > m`, so it is not an `m`-junta either. -/
theorem filmus_ihringer_explicit_family
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ (ℓ n : ℕ) (ι : Fin ℓ × Fin (min d k) → Fin n),
      Function.Injective ι ∧
      2 * (ℓ * min d k) ≤ n ∧
      m < ℓ * min d k ∧
      IsBoolean (restrict (k := k) (witnessPoly (min d k) ℓ ι)) ∧
      DegreeLE d (restrict (k := k) (witnessPoly (min d k) ℓ ι)) ∧
      ¬ IsJunta (ℓ * min d k) (restrict (k := k) (witnessPoly (min d k) ℓ ι)) := by
  sorry

end Agent040
