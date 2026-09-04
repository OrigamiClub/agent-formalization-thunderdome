import Mathlib

open MvPolynomial

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize all three parts of the statement:
* `filmus_ihringer_junta`     — the junta upper bound for `k ≥ 2d`;
* `filmus_ihringer_tightness` — the converse (failure of the bound) for `1 ≤ k < 2d`;
* `filmus_ihringer_witness`   — the explicit witnessing family for the converse.
-/

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
def Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of a slice element, as an argument to a real polynomial. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* on the slice: it agrees on the whole slice with the evaluation,
at the indicator vector, of a **multilinear** real polynomial of total degree `≤ d`.
Multilinearity is spelled out as: every monomial in the support uses each variable at
most once (`t i ≤ 1`). -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *m-junta*: some coordinate set `J` with `|J| ≤ m` determines `f`, i.e.
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The `i`-th block of `e` consecutive coordinates, `{i*e, i*e+1, …, i*e+e-1}`,
intersected with `Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- Explicit witness family.  On the slice `binom([n],k)` this is the function
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, i.e. the number of the first `ℓ` length-`e`
blocks of coordinates that are fully contained in `S`.  (Under the hypotheses of
`filmus_ihringer_witness` at most one such block can be contained in `S`, so the value
is in `{0,1}`.) -/
def witnessFn (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  (((Finset.range ℓ).filter (fun i => block n e i ⊆ S.1)).card : ℝ)

/-- **Filmus–Ihringer, junta direction.**
For every `d ≥ 1` there is a bound `M d` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n],k)` is an `M d`-junta.
(`m(d)` is carried as an existentially quantified `M : ℕ → ℕ`.) -/
theorem filmus_ihringer_junta :
    ∃ M : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
      ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f (M d) := by
  sorry

/-- **Filmus–Ihringer, tightness direction.**
For every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, the junta bound fails: for every `m`
there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_tightness :
    ∀ d : ℕ, 1 ≤ d →
    ∀ k : ℕ, 1 ≤ k → k < 2 * d →
    ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnesses for the tightness direction.**
With `e = min d k` and `1 ≤ k < 2d`, for every `ℓ` and every `n ≥ 2ℓe` the function
`witnessFn n k e ℓ` — namely `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` — is a Boolean
degree-`d` function on `binom([n],k)` that is not an `m`-junta for any `m < ℓe`
(equivalently: it genuinely depends on all `ℓe` coordinates `1,…,ℓe`, so it is not an
`(ℓe−1)`-junta). -/
theorem filmus_ihringer_witness :
    ∀ d : ℕ, 1 ≤ d →
    ∀ k : ℕ, 1 ≤ k → k < 2 * d →
    ∀ ℓ : ℕ, ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
      IsBoolean (witnessFn n k (min d k) ℓ) ∧
      HasDegreeLE (witnessFn n k (min d k) ℓ) d ∧
      ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (witnessFn n k (min d k) ℓ) m := by
  sorry

end FilmusIhringer
