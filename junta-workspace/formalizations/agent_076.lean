/-
  Agent 076 — Formalization of the *statement* only.

  Theorem (Filmus–Ihringer): Boolean constant-degree functions on the slice
  `binom([n],k)` are juntas, with a sharp threshold at `k = 2d`.

  This file states three theorems (all `:= by sorry`, no proofs):

  * `filmus_ihringer_forward`  — the junta upper bound for `k ≥ 2d`.
  * `filmus_ihringer_converse` — for `1 ≤ k < 2d`, no uniform junta bound.
  * `filmus_ihringer_converse_witness` — the explicit witnessing family.

  See `agent_076.md` for the encoding decisions and caveats.
-/

import Mathlib

namespace Agent076

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` real indicator vector of a slice point, used to evaluate polynomials. -/
def sliceIndicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- A multilinear multivariate polynomial: no variable appears to a power `≥ 2`
    in any monomial of the support. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ c ∈ p.support, ∀ i, c i ≤ 1

/-- `f` has *degree ≤ d* on the slice: it agrees, on every slice point, with a
    multilinear real polynomial of total degree `≤ d` evaluated at the `0/1`
    indicator vector. (Equivalently: `f` is an `ℝ`-linear combination of products
    of at most `d` distinct coordinates.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an *`m`-junta*: there is a coordinate set `J` with `|J| ≤ m` such that
    the value of `f` at a slice point `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-! ### Forward direction: junta bound for `k ≥ 2d`. -/

/-- For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d`
    and `n ≥ 2k`, every Boolean degree-`≤ d` function on the slice `binom([n],k)`
    is an `m`-junta.  Here `m(d)` is packaged as an existential natural number. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-! ### Converse: no uniform junta bound when `1 ≤ k < 2d`. -/

/-- If `1 ≤ k < 2d` then for every `m` there is some `n ≥ 2k` and a Boolean
    degree-`≤ d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2d : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ### The explicit witnessing family.

With `e := min d k` and `ℓ` blocks `B_1, …, B_ℓ` of `e` consecutive coordinates
each (`B_i = {(i-1)e+1, …, ie}`), consider

    g(S) = Σ_{i=1}^{ℓ} Π_{j=1}^{e} x_{(i-1)e+j}   evaluated at the indicator of S,

i.e. the number of blocks entirely contained in `S`.  Since `1 ≤ k < 2d` forces
`k < 2e`, at most one block can be contained in `S`, so `g` is Boolean; and each
monomial has degree `e ≤ d`.  For `n ≥ 2ℓe` it depends on all `ℓe` block
coordinates and drops none of them, so it fails to be an `m`-junta for every
`m < ℓe`; letting `ℓ → ∞` defeats any fixed `m`.

(The problem statement writes the family as `Π_i (Σ_j x_{(i-1)e+j})`; see
`agent_076.md` for why the `Σ_i Π_j` monomial form is used here.) -/

/-- Coordinate `(i-1)e + j` (0-indexed: `i * e + j`) of block `i`, as an element
    of `Fin n`, given that all `ℓ * e` block coordinates fit, i.e. `ℓ * e ≤ n`. -/
def blockCoord (d k ℓ n : ℕ) (hℓ : ℓ * min d k ≤ n)
    (i : Fin ℓ) (j : Fin (min d k)) : Fin n :=
  Fin.castLE hℓ (finProdFinEquiv (i, j))

/-- `g(S) = Σ_{i} Π_{j} x_{blockCoord i j}` evaluated at the indicator of `S`:
    the number of blocks fully contained in `S`. -/
def juntaWitness (d k ℓ n : ℕ) (hℓ : ℓ * min d k ≤ n) (S : Slice n k) : ℝ :=
  ∑ i : Fin ℓ, ∏ j : Fin (min d k), sliceIndicator S (blockCoord d k ℓ n hℓ i j)

/-- For `1 ≤ k < 2d`, every number `ℓ` of blocks, and every `n ≥ 2ℓe`
    (`e := min d k`), the function `juntaWitness` is Boolean, has degree `≤ d`,
    and is not an `m`-junta for any `m < ℓ * e`.  Consequently, ranging over `ℓ`,
    it witnesses `filmus_ihringer_converse`. -/
theorem filmus_ihringer_converse_witness
    (d k ℓ n : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2d : k < 2 * d)
    (hℓ : ℓ * min d k ≤ n) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (juntaWitness d k ℓ n hℓ) ∧
    HasDegreeLE (juntaWitness d k ℓ n hℓ) d ∧
    (∀ m : ℕ, m + 1 ≤ ℓ * min d k → ¬ IsJunta (juntaWitness d k ℓ n hℓ) m) := by
  sorry

end Agent076
