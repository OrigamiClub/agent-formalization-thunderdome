import Mathlib

open MvPolynomial

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.
-/

/-- The slice `binom([n], k)`: `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Real `0/1` indicator vector of a subset of `Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f : Slice n k → ℝ` is *Boolean*: every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`*: on the slice it agrees with the evaluation, at the
`0/1` indicator vector, of some real multivariate polynomial of total degree `≤ d`.
On `0/1` inputs such a polynomial may be taken multilinear without loss of
generality, so no multilinearity hypothesis is imposed. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = eval (indicator S.1) p

/-- `f` is an *`m`-junta*: some coordinate set `J` with `|J| ≤ m` determines `f`,
i.e. `f` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ### Forward direction (`k ≥ 2d` ⟹ junta) -/

/-- Filmus–Ihringer, main direction: for every `d ≥ 1` there is a bound `m(d)`
(the existentially quantified `m`, which depends only on `d`) such that on every
slice `binom([n], k)` with `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d`
function is an `m(d)`-junta. -/
theorem filmus_ihringer_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-! ### Converse direction (`1 ≤ k < 2d` ⟹ sharpness) -/

/-- Filmus–Ihringer, sharpness: if `1 ≤ k < 2d` then the junta bound fails on the
`k`-slice — for every `m` there is a slice `binom([n], k)` (with `n ≥ 2k`)
carrying a Boolean degree-`d` function that is not an `m`-junta. -/
theorem filmus_ihringer_sharp (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ### Explicit witnessing family (stated for `1 ≤ k ≤ d`) -/

/-- Coordinates `{ i·ℓ, …, i·ℓ + ℓ - 1 }` of `Fin n`: the `i`-th block of size `ℓ`. -/
def block (n ℓ i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => i * ℓ ≤ (a : ℕ) ∧ (a : ℕ) < i * ℓ + ℓ)

/-- The witness polynomial `∏_{i < e} (∑_{a ∈ block i} X a)`: a product of `e`
disjoint linear forms, one per block of size `ℓ`.  This is the task's family
`∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` with the two ranges read as `e` outer
factors of inner width `ℓ` (`e = min d k`), which is what keeps the total degree
equal to `e ≤ d`. -/
def witnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range e, ∑ a ∈ block n ℓ i, (X a : MvPolynomial (Fin n) ℝ)

/-- For `1 ≤ k ≤ d` (so `min d k = k`) and any block size `ℓ ≥ 1`, on a slice
`binom([n], k)` with `n ≥ 2kℓ`, the function induced by `witnessPoly n ℓ k` — on
`S` it evaluates to `∏_{i < k} |S ∩ block i|`, i.e. the indicator that `S` is a
transversal of the `k` blocks — is Boolean, has degree `≤ d`, and is not an
`m`-junta for any `m < kℓ`.  Letting `ℓ → ∞` gives functions of unbounded junta
size, witnessing sharpness on the `k`-slice. -/
theorem filmus_ihringer_witness
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 2 * k * ℓ ≤ n) :
    IsBoolean (fun S : Slice n k => eval (indicator S.1) (witnessPoly n ℓ k)) ∧
    HasDegreeLE (fun S : Slice n k => eval (indicator S.1) (witnessPoly n ℓ k)) d ∧
    (∀ m : ℕ, m < k * ℓ →
      ¬ IsJunta (fun S : Slice n k => eval (indicator S.1) (witnessPoly n ℓ k)) m) := by
  sorry

end FilmusIhringer
