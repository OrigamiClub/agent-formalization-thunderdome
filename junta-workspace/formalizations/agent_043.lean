import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends with `:= by sorry`; nothing is proved.

We state three things:

* `juntaBound`      — the positive direction, with `m(d)` an existential constant;
* `juntaBound_sharp` — sharpness of the hypothesis `k ≥ 2d`;
* `blockFn_witness`  — the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.
-/

open Finset

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}` indicator vector of a set, as a real point of the cube `(Fin n) → ℝ`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : (Fin n) → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, at every point of the slice, with
the evaluation at the indicator vector of some real multivariate polynomial of total
degree `≤ d`.  (Since indicator vectors are `{0,1}`-valued, such a polynomial can always
be taken multilinear, so no multilinearity hypothesis is imposed.) -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` depends only on the trace `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The polynomial `∏_{i<ℓ} ∑_{j<e} X_{(i,j)}`: a product of `ℓ` linear forms over
disjoint blocks of `e` variables each, with variables indexed by `Fin ℓ × Fin e`. -/
noncomputable def blockForm (ℓ e : ℕ) : MvPolynomial (Fin ℓ × Fin e) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (i, j)

/-- The Filmus–Ihringer witness function on `Slice n k`.  Relabel the variables of
`blockForm ℓ e` onto the first `ℓ * e` coordinates of `Fin n` — block `i`, offset `j`
goes to coordinate `e * i + j` via `finProdFinEquiv` followed by `Fin.castLE` — and
evaluate at indicator vectors.  This is the function
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. -/
noncomputable def blockFn (n k ℓ e : ℕ) (hle : ℓ * e ≤ n) : Slice n k → ℝ :=
  fun S =>
    MvPolynomial.eval (indicator S.1)
      (MvPolynomial.rename
        (fun v : Fin ℓ × Fin e => Fin.castLE hle (finProdFinEquiv v))
        (blockForm ℓ e))

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`≤ d` function on `binom([n], k)` is an `m`-junta. -/
theorem juntaBound (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Filmus–Ihringer, sharpness of `k ≥ 2d`.**
For every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, the junta bound fails: for every `m`
there is some `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is not
an `m`-junta. -/
theorem juntaBound_sharp (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Explicit witnessing family.**
With `e = min d k` and `1 ≤ k < 2d`, for any number of blocks `ℓ` and any
`n ≥ 2 * (ℓ * e)`, the function `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` on `binom([n],k)`
is Boolean, has degree `≤ d`, and is not an `(ℓ * e)`-junta. -/
theorem blockFn_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k) (ℓ : ℕ)
    (n : ℕ) (hle : ℓ * e ≤ n) (hn : 2 * (ℓ * e) ≤ n) :
    IsBoolean (blockFn n k ℓ e hle) ∧
      HasDegreeLE d (blockFn n k ℓ e hle) ∧
      ¬ IsJunta (ℓ * e) (blockFn n k ℓ e hle) := by
  sorry

end FilmusIhringer
