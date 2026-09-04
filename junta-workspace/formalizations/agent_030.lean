import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every `theorem` ends in `:= by sorry`; nothing is proved.

We state:
* the forward direction (`k ≥ 2d`, `n ≥ 2k` ⇒ every Boolean degree-`d` function is an
  `m(d)`-junta, with `m(d)` existentially quantified);
* the converse in existential form (`1 ≤ k < 2d` ⇒ no uniform junta bound);
* the converse with the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`.
-/

/-- The slice `binom([n], k)` = `{ S ⊆ {1,…,n} : |S| = k }`, encoded as the subtype of
`Finset (Fin n)` of sets of cardinality `k`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- Indicator (`0/1`) vector in `ℝ^n` of a slice element. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if all of its values are `0` or `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice: it agrees, at every point of the slice,
with the evaluation at the indicator vector of some real polynomial of total degree `≤ d`.
On `0/1` inputs such a polynomial may always be taken multilinear without increasing its
total degree, so multilinearity is not imposed separately. -/
def HasDegreeAtMost {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    MvPolynomial.totalDegree p ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, forward direction.**
For every `d ≥ 1` there is a constant `m = m(d)` such that: for all `k ≥ 2d` and all
`n ≥ 2k`, every Boolean degree-`d` function on `binom([n], k)` is an `m`-junta. -/
theorem boolean_degree_junta_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanValued f → HasDegreeAtMost f d → IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, converse direction (existential form).**
If `1 ≤ k < 2d` then no uniform junta bound exists: for every `m` there are `n ≥ 2k`
and a Boolean degree-`d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem boolean_degree_junta_converse
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ,
        IsBooleanValued f ∧ HasDegreeAtMost f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit polynomial `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, with the `ℓ`
consecutive blocks of size `e` presented abstractly as `B 0, …, B (ℓ-1)`. -/
noncomputable def blockPoly {n : ℕ} (B : ℕ → Finset (Fin n)) (ℓ : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ v ∈ B i, MvPolynomial.X v

/-- The function that `blockPoly B ℓ` induces on the slice `binom([n], k)`. -/
noncomputable def blockFun {n k : ℕ} (B : ℕ → Finset (Fin n)) (ℓ : ℕ) :
    Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (blockPoly B ℓ)

/-- **Filmus–Ihringer, converse direction — explicit witnesses.**
Let `1 ≤ k < 2d` and `e = min d k`.  Given `ℓ ≥ 1` and any `ℓ` pairwise-disjoint blocks
`B 0, …, B (ℓ-1) ⊆ Fin n` of size `e` (which exist once `n ≥ 2ℓe`; concretely one takes
`B i = { i·e, …, i·e + e − 1 }`), the induced function
`∏_{i<ℓ} (∑_{v ∈ B i} x_v)` on `binom([n], k)` is Boolean, has degree `≤ d`, and is not
an `m`-junta whenever `m < ℓe`.  Since `ℓe → ∞` as `ℓ → ∞`, this contradicts any uniform
junta bound (the paper's phrase "not `ℓe`-juntas" is read here as: the minimal junta size
is `ℓe`, hence the function is not an `m`-junta for any `m < ℓe`). -/
theorem boolean_degree_junta_converse_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (n : ℕ) (hn : 2 * ℓ * e ≤ n)
    (B : ℕ → Finset (Fin n))
    (hcard : ∀ i : ℕ, i < ℓ → (B i).card = e)
    (hdisj : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → Disjoint (B i) (B j))
    (m : ℕ) (hm : m < ℓ * e) :
    IsBooleanValued (blockFun (k := k) B ℓ) ∧
      HasDegreeAtMost (blockFun (k := k) B ℓ) d ∧
      ¬ IsJunta (blockFun (k := k) B ℓ) m := by
  sorry

end FilmusIhringer
