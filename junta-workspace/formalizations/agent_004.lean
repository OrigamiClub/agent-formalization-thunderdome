import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every `theorem` ends in `:= by sorry`; nothing is
proved.

Reference: Yuval Filmus, Ferdinand Ihringer, *Boolean constant degree functions
on the slice are juntas*.
-/

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `{1, …, n}`, encoded as
`k`-element `Finset`s of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of a slice element. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice: it agrees, at every slice point, with the
evaluation at the indicator vector of some real polynomial of total degree `≤ d`.

Multilinearity of the representing polynomial is *not* imposed: on `{0,1}`
coordinates one has `xᵢ^2 = xᵢ`, so a polynomial can always be reduced to a
multilinear one of the same values and no larger total degree. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
the value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Filmus–Ihringer (both directions).**

Fix `d ≥ 1`.

* *Junta side.*  There is a constant `M = m(d)` (existentially quantified here,
  depending only on `d`) such that: if `k ≥ 2d` then for every `n ≥ 2k`, every
  Boolean degree-`≤ d` function on `binom([n], k)` is an `M`-junta.

* *Sharpness side.*  If `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a
  Boolean degree-`≤ d` function on `binom([n], k)` that is *not* an `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f M)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
          IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m) := by
  sorry

/-!
## Explicit sharpness witness

The functions `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e + j} )` with `e = min d k`.
Coordinates are packaged as `ℓ` disjoint blocks of size `e` inside `Fin n`.
-/

/-- Embedding of `ℓ` disjoint blocks of size `e` into `Fin n` (requires
`ℓ * e ≤ n`): the pair `(i, j)` is sent to coordinate `i * e + j`. -/
def blockEmb {ℓ e n : ℕ} (h : ℓ * e ≤ n) : Fin ℓ × Fin e → Fin n :=
  fun p => Fin.castLE h (finProdFinEquiv p)

/-- The explicit witnessing family
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e + j} )`, read as a real-valued function on
the slice by substituting the indicator vector for `x`. -/
def famFn (k ℓ e n : ℕ) (h : ℓ * e ≤ n) : Slice n k → ℝ :=
  fun S => ∏ i : Fin ℓ, ∑ j : Fin e, indicator S (blockEmb h (i, j))

/-- **Explicit witness for the sharpness side.**

Let `1 ≤ k < 2d` and `e = min d k`.  For every block count `ℓ` and every
`n ≥ 2·ℓ·e` (with also `n ≥ 2k`), the function `famFn k ℓ e n` is Boolean on the
slice `binom([n], k)`, has degree `≤ d` on the slice, and is not an `ℓ·e`-junta.
Since `ℓ` is arbitrary, this defeats every fixed junta bound `m`. -/
theorem filmus_ihringer_explicit_witness
    (d k ℓ e : ℕ) (hd : 1 ≤ d) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (he : e = min d k) (n : ℕ) (hn : 2 * (ℓ * e) ≤ n) (hnk : 2 * k ≤ n) :
    IsBoolean (famFn k ℓ e n (by omega)) ∧
    HasDegreeLE (famFn k ℓ e n (by omega)) d ∧
    ¬ IsJunta (famFn k ℓ e n (by omega)) (ℓ * e) := by
  sorry

end FilmusIhringer
