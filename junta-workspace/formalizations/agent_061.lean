import Mathlib

/-!
# Junta threshold for Boolean degree `d` functions on the slice (Filmus; Filmus–Ihringer)

This file formalizes the **statement only** of the following theorem. Every `theorem`
ends in `:= by sorry`; nothing is proved.

> Let `d ≥ 1`. There is a constant `m(d)` such that: if `k ≥ 2d` then for every `n ≥ 2k`,
> every Boolean degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta.
> Conversely, if `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a Boolean
> degree-`d` function on `binom([n],k)` that is not an `m`-junta.

References:
* Y. Filmus, *Junta threshold for low degree Boolean functions on the slice*,
  arXiv:2203.04760, Theorem 1.1.
* Y. Filmus, F. Ihringer, *Boolean constant degree functions on the slice are juntas*,
  arXiv:1801.06338.

See `agent_061.md` for the encoding decisions and known uncertainties.
-/

namespace Agent061

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality `k`.
A slice point is identified with the `0/1` vector of Hamming weight `k` that is its
indicator (see `Slice.ind`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real-valued `0/1` indicator vector of a slice point. -/
def Slice.ind {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A function on the slice *has degree `≤ d`* if it agrees, at every slice point, with the
evaluation at the indicator vector of some real polynomial of total degree `≤ d`.

(Restricting `P` to be multilinear would give an equivalent notion, since multilinearizing a
polynomial does not increase its total degree; we do not impose it.) -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin n) ℝ,
    P.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (Slice.ind S) P

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the value
of `f` at a slice point `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-! ## Upper bound: for `k ≥ 2d` every Boolean degree `d` function is a bounded junta -/

/-- **Junta threshold, easy direction.**
For every `d ≥ 1` there is a constant `m(d)` (existentially quantified here) such that
whenever `2d ≤ k` and `2k ≤ n`, every Boolean function of degree `≤ d` on `binom([n],k)`
is an `m(d)`-junta. -/
theorem junta_threshold_upper :
    ∀ d : ℕ, 1 ≤ d → ∃ m : ℕ,
      ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-! ## Lower bound: for `1 ≤ k < 2d` the junta size is unbounded -/

/-- **Junta threshold, sharpness (abstract form).**
For every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, and every `m`, there is a slice
`binom([n],k)` with `2k ≤ n` carrying a Boolean function of degree `≤ d` that is not an
`m`-junta. -/
theorem junta_threshold_converse :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ### The explicit witnessing family

Put `e = min d k`. Split the first `ℓ·e` coordinates into `ℓ` consecutive blocks
`B_i = {(i-1)e+1, …, ie}` of size `e` and take the sum of the block monomials
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`.

* Since `2·min d k > k` whenever `1 ≤ k < 2d`, at most one block can be contained in a
  `k`-set, so on the slice this sum is `0/1`-valued (Boolean).
* Every monomial has degree `e = min d k ≤ d`, so the function has degree `≤ d`.
* For `n ≥ 2ℓe` the function is not an `(ℓe − 1)`-junta (block coordinates vs. `ℓe` fresh
  coordinates), so taking `ℓ → ∞` — the degree bound `e ≤ d` is untouched — defeats every
  fixed junta bound `m`. -/

/-- The block monomial `∏_{j < e} x_{i·e + j}` in `MvPolynomial (Fin n) ℝ`.
An out-of-range coordinate contributes a `0` factor; under the hypotheses of
`junta_threshold_converse_explicit` no coordinate is out of range. -/
noncomputable def blockMonomial (n e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The polynomial `∑_{i < ℓ} ∏_{j < min d k} x_{i·(min d k) + j}`. -/
noncomputable def FIpoly (n d k ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, blockMonomial n (min d k) i

/-- The function on the slice `binom([n],k)` induced by `FIpoly`. -/
noncomputable def FIfun (n d k ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (Slice.ind S) (FIpoly n d k ℓ)

/-- **Junta threshold, sharpness (explicit witnesses).**
For `1 ≤ k < 2d` and any `m`, there are `ℓ ≥ 1` and `n` with `2k ≤ n` and
`2ℓ·(min d k) ≤ n` such that the function
`FIfun n d k ℓ = ∑_{i<ℓ} ∏_{j<min d k} x_{i·(min d k)+j}` on `binom([n],k)` is Boolean,
has degree `≤ d`, and is not an `m`-junta. -/
theorem junta_threshold_converse_explicit
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ,
      1 ≤ ℓ ∧ 2 * k ≤ n ∧ 2 * ℓ * min d k ≤ n ∧
      IsBoolean (FIfun n d k ℓ) ∧
      HasDegreeLE d (FIfun n d k ℓ) ∧
      ¬ IsJunta m (FIfun n d k ℓ) := by
  sorry

end Agent061
