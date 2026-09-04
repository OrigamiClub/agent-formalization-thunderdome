/-
Agent 090 — Formalization diversity study
Statement only. Every theorem ends in `:= by sorry`; nothing is proved.

THEOREM (Filmus–Ihringer / Filmus, "Junta threshold for low degree Boolean
functions on the slice"):
Boolean constant-degree functions on the slice `binom([n],k)` are juntas, with a
threshold at `k = 2d`.

  * Positive: for `d ≥ 1` there is `m(d)` such that if `k ≥ 2d` then for every
    `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
    `m(d)`-junta.
  * Converse: if `1 ≤ k < 2d` then for every `m` there are `n ≥ 2k` and a
    Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta,
    witnessed by an explicit block family.

See `agent_090.md` for the encoding decisions and caveats.
-/
import Mathlib

open scoped BigOperators

namespace Agent090

/-- The indicator vector of `S ⊆ Fin n`, as a point of `ℝ^n` (i.e. `Fin n → ℝ`).
Evaluating a polynomial here is how "degree" is transported to the slice. -/
def sliceIndicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on subsets of `Fin n` is **Boolean on the `k`-slice**
`binom([n],k) = {S : |S| = k}` if it takes values in `{0,1}` there. -/
def BooleanOnSlice {n : ℕ} (k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has **degree `≤ d` on the `k`-slice**: on the slice it agrees with the
evaluation, at the indicator vector, of a *multilinear* real polynomial of total
degree `≤ d`. (Multilinearity is `μ i ≤ 1` for every exponent vector `μ` in the
support; it is harmless since `x_i^2 = x_i` on `{0,1}` inputs, but it matches the
wording of the theorem.) -/
def SliceDegreeLE {n : ℕ} (k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ μ ∈ p.support, ∀ i, μ i ≤ 1) ∧
    ∀ S : Finset (Fin n), S.card = k →
      f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an **`m`-junta on the `k`-slice**: there is a coordinate set `J` with
`|J| ≤ m` such that the value of `f` on any slice element `S` depends only on
`S ∩ J`. -/
def JuntaOnSlice {n : ℕ} (k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      S ∩ J = T ∩ J → f S = f T

/-!
### Positive direction
-/

/-- **Positive direction.** For every `d ≥ 1` there is a bound `m(d)` (here an
existential `m`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta.

`n ≥ 2k` gives `k ≥ 2d` and `n - k ≥ 2d`, i.e. both `k` and `n-k` are large. -/
theorem filmus_ihringer_positive (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        BooleanOnSlice k f → SliceDegreeLE k d f → JuntaOnSlice k m f := by
  sorry

/-!
### Converse direction (tightness at `k = 2d`)
-/

/-- **Converse direction.** If `1 ≤ k < 2d` then no uniform junta bound exists:
for every `m` there are `n ≥ 2k` and a Boolean degree-`d` function on
`binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Finset (Fin n) → ℝ,
        BooleanOnSlice k f ∧ SliceDegreeLE k d f ∧ ¬ JuntaOnSlice k m f := by
  sorry

/-!
### Explicit witnessing family

With `e = min d k`, the block `consecBlock e i n` is the `i`-th run of `e`
consecutive coordinates `{i·e, …, i·e + e - 1} ⊆ Fin n`.

The theorem's family is written `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`.  The
`{0,1}`-valued, degree-`≤ d` object this refers to (see the note) is the
sum-of-products / "some block is fully contained" indicator
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, evaluated at the indicator vector of `S`:
that is `filmusFamily d k ℓ n`.  Because `k < 2d` forces `2e > k`, at most one
block can be contained in a `k`-set, so the sum is genuinely `{0,1}`-valued.
-/

/-- The `i`-th block of `e` consecutive coordinates of `Fin n`. -/
def consecBlock (e i n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The explicit witnessing family, `e := min d k`:
`filmusFamily d k ℓ n S = ∑_{i<ℓ} [ block i ⊆ S ]`
`  = ∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` evaluated at the indicator of `S`. -/
def filmusFamily (d k ℓ n : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range ℓ, (if consecBlock (min d k) i n ⊆ S then (1 : ℝ) else 0)

/-- **Explicit form of the converse.** For `1 ≤ k < 2d` and any `m`, taking
enough blocks `ℓ` (so `ℓ · min d k > m`) and `n` with `n ≥ 2k` and
`n ≥ 2 · ℓ · min d k`, the function `filmusFamily d k ℓ n` is a Boolean
degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_explicit_family (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∃ n : ℕ, 2 * k ≤ n ∧ 2 * ℓ * min d k ≤ n ∧
        BooleanOnSlice k (filmusFamily d k ℓ n) ∧
        SliceDegreeLE k d (filmusFamily d k ℓ n) ∧
        ¬ JuntaOnSlice k m (filmusFamily d k ℓ n) := by
  sorry

end Agent090
