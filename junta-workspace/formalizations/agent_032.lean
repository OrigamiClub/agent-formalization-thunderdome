import Mathlib

/-!
Agent 032 — Filmus–Ihringer:
"Boolean constant-degree functions on the slice are juntas."

Statement only. Every theorem ends in `:= by sorry`; nothing is proved.

We formalize all three parts of the statement:
* `filmus_ihringer_junta_bound` — forward direction (upper bound),
* `filmus_ihringer_not_junta`   — converse (lower bound), existential form,
* `filmus_ihringer_witness`     — the explicit witnessing family.
-/

namespace Agent032

open scoped BigOperators

/-- The slice `binom([n], k) = {S ⊆ {1,…,n} : |S| = k}`, encoded as the `k`-element
subsets of `Fin n`. `abbrev` so that `.1 / .val` projections unfold transparently. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- A function on the slice is *Boolean* if it takes values in `{0, 1} ⊆ ℝ`. -/
def IsBooleanFun {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ x : Slice n k, f x = 0 ∨ f x = 1

/-- `f` has *degree `≤ d`* on the slice: there is a multilinear real polynomial `p` of total
degree `≤ d` such that on every point `S` of the slice, `f S` equals the evaluation of `p`
at the `0/1` indicator vector of `S`.

* Multilinearity is encoded as "every exponent occurring in every monomial of `p.support`
  is `≤ 1`".
* Since this is an existential over `p`, it captures the *minimal-degree representative*
  notion of degree on the slice (representatives differing by a multiple of `Σ xᵢ - k`
  agree on the slice). -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ x : Slice n k,
      f x = MvPolynomial.eval (fun i => if i ∈ x.1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the value
of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ x y : Slice n k, x.1 ∩ J = y.1 ∩ J → f x = f y

/-- **Forward direction (upper bound).**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`≤ d` function on `binom([n], k)` is an `m`-junta.

The constant `m(d)` is stated as an existential (`∃ m : ℕ`), with `d` a fixed parameter. -/
theorem filmus_ihringer_junta_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanFun f → HasSliceDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse (lower bound), existential form.**
If `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a Boolean degree-`≤ d` function
on `binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBooleanFun f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witnessing family

`f(S) = ∏_{i=0}^{ℓ-1} ( Σ_{j=0}^{e-1} [ (i*e + j) ∈ S ] )`,

i.e. the product, over `ℓ` consecutive blocks of length `e`, of the number of elements of
`S` lying in that block. The coordinate `i*e + j` of `Fin n` is identified with the natural
number `i*e + j` (no wraparound; the relevant range `ℓ*e ≤ n` is supplied by the
hypothesis `hn` in the theorem below). Indexing is `0`-based. -/
noncomputable def witnessFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i ∈ Finset.range ℓ,
    ((S.1.filter (fun x => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)).card : ℝ)

/-- **Explicit witness.**
With `e = min d k`, `ℓ ≥ 1`, and `n ≥ 2 * (ℓ * e)`, the function `witnessFun n k e ℓ` is
Boolean, has slice-degree `≤ d`, and is not an `(ℓ * e)`-junta.

Together with monotonicity of `IsJunta` in `m` (a `≤ m`-junta is a `≤ m'`-junta for
`m ≤ m'`), choosing `ℓ` with `ℓ * e ≥ m` recovers `filmus_ihringer_not_junta`. -/
theorem filmus_ihringer_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (n : ℕ) (hn : 2 * (ℓ * e) ≤ n) :
    IsBooleanFun (witnessFun n k e ℓ) ∧
    HasSliceDegreeLE d (witnessFun n k e ℓ) ∧
    ¬ IsJunta (ℓ * e) (witnessFun n k e ℓ) := by
  sorry

end Agent032
