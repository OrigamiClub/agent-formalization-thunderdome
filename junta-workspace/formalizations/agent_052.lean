/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

STATEMENT-ONLY formalization.  Every theorem ends in `:= by sorry`; nothing is
proved.  Written from knowledge of Mathlib without a compiler, so some library
identifiers are best guesses (see `agent_052.md`).

What is stated:
  * `filmus_ihringer` — BOTH directions:
      - forward: for `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`≤ d` function
        on the slice `binom([n], k)` is an `m(d)`-junta, where the constant
        `m = m(d)` depends only on `d` (rendered as `∃ m : ℕ` after `d` is fixed);
      - converse: for `1 ≤ k < 2d`, for every `m` there are `n ≥ 2k` and a
        Boolean degree-`≤ d` function on `binom([n], k)` that is not an `m`-junta.
  * `filmus_ihringer_witness` — the explicit lower-bound family
        `f(S) = ∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`,  `e = min d k`
    provides those counterexamples: for every `m` there are `ℓ, n` for which the
    family member is Boolean, has degree `≤ d`, and is not an `m`-junta.
    (See the note for why this is the sum-of-products, not the product-of-sums.)
-/
import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`
(a stand-in for `{1, …, n}`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of a slice element, as a point of `ℝ^n`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the
values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, on every slice element,
with the evaluation at that element's indicator vector of some real polynomial
of total degree `≤ d`.

(Demanding the polynomial be multilinear, as in the informal statement, does not
change the class of functions obtained: on `{0,1}` one has `xᵢ² = xᵢ`, so any
polynomial can be reduced to a multilinear one without increasing its total
degree.  We therefore record only the total-degree bound.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

* (forward) There is a constant `m = m(d)` such that whenever `k ≥ 2d` and
  `n ≥ 2k`, every Boolean degree-`≤ d` function on `binom([n], k)` is an
  `m`-junta.
* (converse) If `1 ≤ k < 2d` then no such constant exists: for every `m` there
  are `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is
  not an `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m) := by
  sorry

/-- Block size `e = min d k` for the explicit family. -/
def blk (d k : ℕ) : ℕ := min d k

/-- The value at coordinate `c` of a slice element `S`, i.e. `x_c` : it is `1`
if `c` (as a natural number) is the index of some element of `S`, else `0`. -/
def coordVal {n k : ℕ} (S : Slice n k) (c : ℕ) : ℝ :=
  ∑ a ∈ S.1, (if (a : ℕ) = c then (1 : ℝ) else 0)

/-- The explicit Filmus–Ihringer lower-bound family, evaluated on the slice:
`f(S) = ∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i·e + j}` with `e = min d k`.

The `i`-th summand is the indicator that the whole `i`-th block of `e`
consecutive coordinates `{i·e, …, i·e + e - 1}` is contained in `S`.  When
`k < 2d` two disjoint full blocks cannot both fit in a `k`-set, so on the slice
this sum is `{0,1}`-valued; its degree as a polynomial in the `x`'s is
`e = min d k ≤ d`. -/
def fam (d k ℓ n : ℕ) (S : Slice n k) : ℝ :=
  ∑ i ∈ Finset.range ℓ,
    ∏ j ∈ Finset.range (blk d k), coordVal S (i * blk d k + j)

/-- The explicit family furnishes the converse's counterexamples: for
`1 ≤ k < 2d` and every `m`, there are `ℓ` and `n ≥ max (2k) (2ℓe)` such that
`fam d k ℓ n` is Boolean, has degree `≤ d` on the slice, and is not an
`m`-junta.  (One may take `ℓ ≈ m`; the minimal junta of `fam d k ℓ n` has
about `ℓ·e` coordinates, so it grows without bound as `ℓ → ∞`.) -/
theorem filmus_ihringer_witness (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ, 2 * k ≤ n ∧ 2 * ℓ * blk d k ≤ n ∧
      IsBoolean (fam d k ℓ n) ∧
      HasDegreeLE (fam d k ℓ n) d ∧
      ¬ IsJunta (fam d k ℓ n) m := by
  sorry

end FilmusIhringer
