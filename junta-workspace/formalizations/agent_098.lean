import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-! # Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends with `:= by sorry`.

We formalize BOTH directions of the dichotomy:

* `boolean_degree_le_junta`         — positive direction (`k ≥ 2d` ⇒ junta),
* `exists_boolean_degree_not_junta` — negative direction (`k < 2d`), with the
  explicit Filmus–Ihringer witnessing family,
* `exists_boolean_degree_not_junta'` — negative direction, plain existential form.
-/

/-! ## Encoding of the slice and of Boolean degree-`d` functions -/

/-- The slice `binom([n], k)`, encoded as the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The real `{0,1}`-indicator vector of a slice element. -/
def slicePoint {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d` on the slice* if it agrees, on the whole slice, with a
multilinear real polynomial of total degree `≤ d` evaluated at the indicator vector.

Multilinearity is expressed as "every exponent occurring in the support is `≤ 1`".
Since the slice is contained in `{0,1}^n`, requiring multilinearity is no loss of
generality (multilinearize by `xᵢ^a ↦ xᵢ`, which does not raise the total degree). -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (slicePoint S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Positive direction: `k ≥ 2d` forces juntas -/

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a constant `M = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`d` function on the slice `binom([n], k)` is an
`M`-junta.  (The constant `M` is stated as an existential, uniform in `k` and `n`.) -/
theorem boolean_degree_le_junta {d : ℕ} (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ (k n : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta M f := by
  sorry

/-! ## Negative direction: `k < 2d` allows non-juntas -/

/-- Witness polynomial `∑_{i < ℓ} ∏_{j < e} X (emb (i, j))`.

`emb` selects `ℓ` pairwise disjoint blocks of `e` coordinates; injectivity of `emb`
encodes both the disjointness of the blocks and the consecutive layout
`x_{(i-1)e + j}` used in the Filmus–Ihringer construction.  (Note: relative to the
prose in the task, the outer `∑` and inner `∏` are as required for the function to be
Boolean of degree `e ≤ d`; see the accompanying note.) -/
noncomputable def witnessPoly {n : ℕ} (ℓ e : ℕ) (emb : Fin ℓ × Fin e ↪ Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin ℓ, ∏ j : Fin e, MvPolynomial.X (emb (i, j))

/-- The witness function on the slice: the witness polynomial evaluated at indicator vectors. -/
noncomputable def witnessFun {n k : ℕ} (ℓ e : ℕ) (emb : Fin ℓ × Fin e ↪ Fin n) :
    Slice n k → ℝ :=
  fun S => MvPolynomial.eval (slicePoint S) (witnessPoly ℓ e emb)

/-- **Filmus–Ihringer, negative direction (with explicit witnessing family).**
If `d ≥ 1` and `1 ≤ k < 2d`, then for every `m` there exist `n ≥ 2k`, a length `ℓ`,
and a choice of `ℓ` disjoint blocks of size `e = min d k` (given by an embedding
`emb`) such that
`witnessFun ℓ e emb = (S ↦ ∑_{i < ℓ} ∏_{j < e} x_{emb (i,j)})`
is a Boolean degree-`d` function on `binom([n], k)` that is not an `m`-junta.
Taking `ℓ` large (so `ℓ·e > m`) defeats any fixed junta size. -/
theorem exists_boolean_degree_not_junta {d : ℕ} (hd : 1 ≤ d)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ (n ℓ : ℕ) (emb : Fin ℓ × Fin (min d k) ↪ Fin n),
      2 * k ≤ n ∧
      IsBoolean (witnessFun (k := k) ℓ (min d k) emb) ∧
      HasSliceDegreeLE d (witnessFun (k := k) ℓ (min d k) emb) ∧
      ¬ IsJunta m (witnessFun (k := k) ℓ (min d k) emb) := by
  sorry

/-- **Filmus–Ihringer, negative direction (plain form).**
If `d ≥ 1` and `1 ≤ k < 2d`, then for every `m` there exist `n ≥ 2k` and a Boolean
degree-`d` function on the slice `binom([n], k)` that is not an `m`-junta. -/
theorem exists_boolean_degree_not_junta' {d : ℕ} (hd : 1 ≤ d)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ (n : ℕ) (f : Slice n k → ℝ),
      2 * k ≤ n ∧ IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

end FilmusIhringer
