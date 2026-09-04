/-
  Agent 094 — Formalization of the *statement* of:

  Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer).

  Statement only.  Every theorem ends in `:= by sorry`; nothing is proved.

  Encoding summary (see agent_094.md for discussion):
    * slice          : `{S : Finset (Fin n) // S.card = k}`
    * Boolean values : real-valued `f` with `∀ S, f S = 0 ∨ f S = 1`
    * degree ≤ d     : agrees on the slice with a *multilinear* `MvPolynomial (Fin n) ℝ`
                       of `totalDegree ≤ d`, evaluated at the 0/1 indicator vector
    * m-junta        : `∃ J, J.card ≤ m ∧ (S ∩ J = T ∩ J → f S = f T)`
    * m(d)           : an existential `∃ m : ℕ` in the forward statement
    * explicit family: `blockPoly` / `blockFun` below, used in
                       `filmus_ihringer_converse_explicit`
-/

import Mathlib

namespace Agent094

open scoped BigOperators

/-- The 0/1 indicator vector of a finset, the input to `MvPolynomial.eval`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- The slice `binom([n], k)` : the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- `f` takes only Boolean values. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: it agrees, on every point of the slice, with a
multilinear real polynomial of total degree `≤ d` evaluated at the indicator vector.
Multilinearity is expressed as "every exponent in every monomial of the support is `≤ 1`". -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that the value
of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ### Explicit witnessing family

`∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`, with `e = min d k`.

Indices are shifted to be 0-based: the `i`-th factor (`i ∈ range ℓ`) is the sum of
`x_{i*e+j}` for `j ∈ range e`.  A variable whose (nat) index is `≥ n` is replaced by `0`;
under the hypothesis `n ≥ 2 * ℓ * e` used in the theorems below, every index `i*e+j` with
`i < ℓ`, `j < e` is `< n`, so this fallback is never triggered. -/

/-- The polynomial `∏_{i<ℓ} Σ_{j<e} X_{i*e+j}` in `MvPolynomial (Fin n) ℝ`. -/
noncomputable def blockPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The Boolean function on the slice induced by `blockPoly` via indicator-vector evaluation. -/
noncomputable def blockFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S.1) (blockPoly n e ℓ)

/-! ### The theorem (Filmus–Ihringer) -/

/-- **Forward direction.**  For every `d ≥ 1` there is a bound `m` (depending only on `d`)
such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`≤ d` function on the slice
`binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse direction (pure existential form).**  If `1 ≤ k < 2d`, then for every `m`
there are `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is *not* an
`m`-junta. -/
theorem filmus_ihringer_converse
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Converse direction, with the explicit witnessing family.**  If `1 ≤ k < 2d`, then for
every `m` there are `n` and `ℓ` with `n ≥ 2k`, `n ≥ 2 * ℓ * e` and `ℓ * e > m`
(where `e = min d k`) such that the function `blockFun n k e ℓ` — induced by
`∏_{i<ℓ} Σ_{j<e} x_{i*e+j}` — is Boolean, has degree `≤ d` on the slice, and is not an
`m`-junta.  (It genuinely depends on all `ℓ * e > m` of its coordinates.) -/
theorem filmus_ihringer_converse_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n ℓ : ℕ,
      2 * k ≤ n ∧
      2 * (ℓ * min d k) ≤ n ∧
      m < ℓ * min d k ∧
      IsBoolean (blockFun n k (min d k) ℓ) ∧
      HasDegreeLE d (blockFun n k (min d k) ℓ) ∧
      ¬ IsJunta m (blockFun n k (min d k) ℓ) := by
  sorry

end Agent094
