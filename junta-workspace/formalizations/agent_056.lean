import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:
* `boolean_degree_junta_pos`   — the positive direction (`k ≥ 2d` ⇒ junta),
* `boolean_degree_junta_neg`   — the negative direction (headline existential form),
* `boolean_degree_junta_neg_explicit` — the explicit witnessing family.

See `agent_056.md` for the encoding rationale and known uncertainties.
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` real indicator vector of a subset `S ⊆ Fin n`. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanF {n k : ℕ} (f : Slice n k → ℝ) : Prop := ∀ S, f S = 0 ∨ f S = 1

/-- A multilinear polynomial: every exponent occurring in the support is `≤ 1`. -/
def IsMultilinearPoly {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ t ∈ p.support, ∀ i, t i ≤ 1

/-- `f` has *degree `≤ d`* on the slice: it agrees on the slice with a multilinear real
polynomial of total degree `≤ d`, evaluated at the `0/1` indicator vector of `S`.

(On the slice, dropping the multilinearity requirement yields the same class of
functions, since `x_i^2 = x_i` on `0/1` inputs; see the note.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinearPoly p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (ind (S : Finset (Fin n))) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-! ## Positive direction -/

/-- **Filmus–Ihringer, positive direction.**  For every `d ≥ 1` there is a constant
`M = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on
the slice `binom([n],k)` is an `M`-junta.

`m(d)` is existentially quantified (the paper's explicit value is `binom(2d,d)`). -/
theorem boolean_degree_junta_pos (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanF f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-! ## Negative direction (headline form) -/

/-- **Filmus–Ihringer, negative direction.**  If `1 ≤ k < 2d` then no junta bound holds:
for every `m` there is some `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)`
that is not an `m`-junta. -/
theorem boolean_degree_junta_neg (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBooleanF f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ## Negative direction (explicit witnessing family) -/

/-- The `i`-th block of `e` consecutive coordinates,
`{ i*e, i*e+1, …, i*e+e-1 } ⊆ Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun c => i * e ≤ (c : ℕ) ∧ (c : ℕ) < i * e + e)

/-- The explicit witness family: a "tribes"-style function, the OR over `i < ℓ` of the
AND of the `i`-th block of `e` coordinates.  As a polynomial this is
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (a sum of `ℓ` pairwise-disjoint degree-`e`
monomials).

On a slice with `k < 2e` at most one term can be `1`, so this function is Boolean; it
has degree `e`. -/
def tribesFun (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∑ i ∈ Finset.range ℓ, (if block n e i ⊆ (S : Finset (Fin n)) then (1 : ℝ) else 0)

/-- **Filmus–Ihringer, explicit negative witnesses.**  For `1 ≤ k < 2d`, put
`e = min d k`.  For every `ℓ` and every large enough `n` (`n ≥ 2k` and `n ≥ 2ℓe`), the
function `tribesFun n k e ℓ` is a Boolean degree-`d` function on `binom([n],k)` that
depends on all `ℓe` block coordinates: it is **not** an `m`-junta for any `m < ℓe`.

(The source phrases the conclusion as "not an `ℓe`-junta"; the precise claim is
non-junta strictly below `ℓe`, equivalently not an `(ℓe − 1)`-junta.) -/
theorem boolean_degree_junta_neg_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (ℓ : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ 2 * ℓ * min d k ≤ n ∧
      IsBooleanF (tribesFun n k (min d k) ℓ) ∧
      HasDegreeLE (tribesFun n k (min d k) ℓ) d ∧
      ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (tribesFun n k (min d k) ℓ) m := by
  sorry

end FilmusIhringer
