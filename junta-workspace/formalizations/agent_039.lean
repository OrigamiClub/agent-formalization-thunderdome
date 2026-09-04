import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Both directions are stated, and the converse
includes the explicit witnessing family
`∏_{i<ℓ} ∑_{j<e} x_{i·e + j}` with `e = min d k`.

Nothing is proved: every theorem ends with `:= by sorry`.
-/

open Finset

namespace FilmusIhringer

/-! ## Setup: the slice, Boolean functions, degree, and juntas -/

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`.
Here `Fin n` plays the role of the ground set `{1, …, n}`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` real indicator vector of a subset of `Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice: it agrees, at every point of the slice, with
the evaluation at the `0/1` indicator vector of some **multilinear** real polynomial of
total degree `≤ d`.  Multilinearity is encoded as "each variable occurs with degree
`≤ 1`", i.e. `MvPolynomial.degreeOf i p ≤ 1`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, p.degreeOf i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Forward direction: constant degree ⟹ junta, for `k ≥ 2d` -/

/-- **Filmus–Ihringer, junta direction.**
For every `d ≥ 1` there is a bound `M d` such that: whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n], k)` is an `M d`-junta. -/
theorem boolean_degree_junta_forward :
    ∃ M : ℕ → ℕ, ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
        ∀ n : ℕ, 2 * k ≤ n →
          ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f (M d) := by
  sorry

/-! ## Converse: for `1 ≤ k < 2d`, no uniform junta bound -/

/-- **Filmus–Ihringer, converse.**
If `1 ≤ k < 2d`, then there is no uniform junta bound.  Writing `e = min d k`, for
every `m` one can choose `ℓ` with `ℓ · e > m` so that, for every `n ≥ 2k` with
`n ≥ 2ℓe`, there is a Boolean degree-`d` function `f` on `binom([n], k)` that is **not**
an `ℓe`-junta (hence not an `m`-junta).

The witness is the block product-of-sums
`f(S) = ∏_{i<ℓ} ( ∑_{j<e} x_{i·e + j} )`,
whose variables are the first `ℓe` coordinates, cut into `ℓ` consecutive blocks of
length `e`.  The coordinate map `c : Fin ℓ → Fin e → Fin n` records this indexing:
`c i j` is the coordinate `i·e + j` (a `0`-indexed version of `x_{(i-1)e+j}`). -/
theorem boolean_degree_junta_converse
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∀ n : ℕ, 2 * k ≤ n → 2 * (ℓ * min d k) ≤ n →
        ∃ f : Slice n k → ℝ,
          IsBoolean f ∧
          HasDegreeLE f d ∧
          ¬ IsJunta f (ℓ * min d k) ∧
          ¬ IsJunta f m ∧
          ∃ c : Fin ℓ → Fin (min d k) → Fin n,
            (∀ i j, (c i j : ℕ) = (i : ℕ) * min d k + (j : ℕ)) ∧
            ∀ S : Slice n k,
              f S = ∏ i : Fin ℓ, ∑ j : Fin (min d k),
                      (if c i j ∈ S.1 then (1 : ℝ) else 0) := by
  sorry

end FilmusIhringer
