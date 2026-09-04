import Mathlib

open scoped BigOperators

namespace Agent006

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends with `:= by sorry`).

We state **both directions** of the dichotomy plus the **explicit witnessing
family** for the converse.  See `agent_006.md` for the encoding rationale and the
interpretation choices made for the witness family.
-/

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real `{0,1}`-indicator vector of a point of the slice. -/
def indicator {n k : ℕ} (s : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ s.1 then (1 : ℝ) else 0

/-- A function on the slice is Boolean if it takes only the values `0` and `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ s : Slice n k, f s = 0 ∨ f s = 1

/-- `f` has degree `≤ d` on the slice: at every point of the slice it agrees with
the evaluation, at the indicator vector, of some real polynomial in the `n`
coordinate variables of total degree `≤ d`.

Restricting `p` to *multilinear* polynomials would give an equivalent notion:
reducing modulo `xᵢ^2 = xᵢ` (valid on `{0,1}` inputs) never raises the total
degree, so both quantifiers describe the same class of functions. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ s : Slice n k, f s = MvPolynomial.eval (indicator s) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ s t : Slice n k, s.1 ∩ J = t.1 ∩ J → f s = f t

/-- **Forward direction.** For every `d ≥ 1` there is a constant `m` (depending
only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`≤ d` function on the slice `binom([n], k)` is an `m`-junta.

The constant `m(d)` is packaged as an existential inside the statement. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanValued f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Converse direction.** If `1 ≤ k < 2d` then for every `m` there exist
`n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is *not* an
`m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBooleanValued f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit witnessing family, in sum-of-products normal form.

With block size `e` and `ℓ` blocks, and an indexing `b` of the `ℓ × e` block
coordinates into `Fin n`, this is the sum of pairwise-disjoint degree-`e`
monomials `∑_{i<ℓ} ∏_{j<e} x_{b i j}`, read as a function on the slice.  (The
family in the theorem is written `∏_i (∑_j x_{(i-1)e+j})`; on the slice, with
`e = min d k` and `k < 2·min d k`, at most one block can be fully contained in a
`k`-set, so that product collapses to this sum of disjoint monomials, which is
manifestly of degree `min d k ≤ d`.  See `agent_006.md`.) -/
def blockFamily {n k : ℕ} (ℓ e : ℕ) (b : Fin ℓ → Fin e → Fin n) :
    Slice n k → ℝ :=
  fun s => ∑ i : Fin ℓ, ∏ j : Fin e, indicator s (b i j)

/-- **Explicit witnesses for the converse.** With `e = min d k`, for every number
of blocks `ℓ ≥ 1` and every `n ≥ 2·ℓ·e` together with an injective indexing `b`
of the block coordinates, the function `blockFamily ℓ e b` on `binom([n], k)`:

* is Boolean valued;
* has degree `≤ d`;
* is not an `m`-junta for any `m < ℓ·e`

(so, taking `ℓ` with `ℓ·e > m`, it defeats any fixed junta bound `m`). -/
theorem blockFamily_spec (d k ℓ : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 2 * ℓ * min d k ≤ n)
    (b : Fin ℓ → Fin (min d k) → Fin n)
    (hb : Function.Injective (fun p : Fin ℓ × Fin (min d k) => b p.1 p.2)) :
    IsBooleanValued (blockFamily (k := k) ℓ (min d k) b) ∧
    HasDegreeLE (blockFamily (k := k) ℓ (min d k) b) d ∧
    (∀ m : ℕ, m < ℓ * min d k →
      ¬ IsJunta (blockFamily (k := k) ℓ (min d k) b) m) := by
  sorry

end Agent006
