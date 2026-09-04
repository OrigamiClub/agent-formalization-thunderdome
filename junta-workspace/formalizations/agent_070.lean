import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:
* the forward direction  (`k ≥ 2d`  ⟹  `m(d)`-junta, with `m(d)` an existential
  depending only on `d`);
* the converse           (`1 ≤ k < 2d`  ⟹  for every `m` a Boolean degree-`d`
  function that is not an `m`-junta);
* the explicit witnessing family.

See `agent_070.md` for the encoding rationale and the caveats.
-/

namespace FilmusIhringer

/-- The slice `binom([n], k)` : subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function on the slice is *Boolean* if all its values lie in `{0, 1}`. -/
def IsBooleanOnSlice {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice if it agrees, at every point of the slice,
with the evaluation at the `0/1` indicator vector of `S` of some real polynomial in the
`n` coordinate variables of total degree at most `d`.

(Over the slice such a `p` may always be taken multilinear; we do not build that in, since
`totalDegree ≤ d` is already the intended constraint.) -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i : Fin n => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Forward direction -/

/-- **Filmus–Ihringer, forward direction.**
Let `d ≥ 1`. There is a constant `M = m(d)` (depending only on `d`) such that whenever
`k ≥ 2d` and `n ≥ 2k`, every Boolean function of degree at most `d` on the slice
`binom([n], k)` is an `M`-junta. -/
theorem boolean_degree_d_on_slice_is_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanOnSlice f → HasDegreeLE d f → IsJunta M f := by
  sorry

/-! ## Converse direction -/

/-- **Filmus–Ihringer, converse direction.**
Let `d ≥ 1`. If `1 ≤ k < 2d`, then for every `m` there exist `n ≥ 2k` and a Boolean
function of degree at most `d` on the slice `binom([n], k)` that is *not* an `m`-junta. -/
theorem boolean_degree_d_on_slice_not_junta (d : ℕ) (hd : 1 ≤ d) :
    ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanOnSlice f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## The explicit witnessing family

With `e := min d k`, partition the first `ℓ * e` coordinates into `ℓ` consecutive blocks
of size `e`, block `i` being `{i*e, i*e+1, …, i*e+e-1}` (`i = 0, …, ℓ-1`).

The witness is `∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i*e+j}` — a real polynomial of total degree
`e ≤ d`.  Evaluated at the indicator vector of `S` it equals the number of blocks entirely
contained in `S`, which we express combinatorially below.  (See `agent_070.md` on why we
read the family as *sum of block-products* rather than the literal product-of-block-sums.)
-/

/-- Value of the witnessing family at `S`: the number of the `ℓ` blocks of size `min d k`
that are entirely contained in `S`.  Block `i` is `{a : Fin n | a / (min d k) = i}`; a
block of size `e` is contained in `S` iff `S` meets it in exactly `e` points. -/
noncomputable def blockFamily (n k d ℓ : ℕ) : Slice n k → ℝ := fun S =>
  (((Finset.range ℓ).filter
      (fun i => (S.1.filter (fun a : Fin n => (a : ℕ) / min d k = i)).card = min d k)).card : ℝ)

/-- **Explicit family witnessing the converse.**
Let `d ≥ 1`, `1 ≤ k < 2d`, put `e := min d k`, and let `ℓ` be arbitrary.  For every
`n ≥ 2 * ℓ * e`, the function `blockFamily n k d ℓ` is Boolean on `binom([n], k)`, has
degree at most `d`, and is not an `m`-junta for any `m < ℓ * e` (it genuinely depends on
all `ℓ * e` block coordinates).  Choosing `ℓ` with `ℓ * e > m` gives the converse. -/
theorem blockFamily_witnesses_non_junta
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * ℓ * min d k ≤ n) :
    IsBooleanOnSlice (blockFamily n k d ℓ) ∧
    HasDegreeLE d (blockFamily n k d ℓ) ∧
    ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (blockFamily n k d ℓ) := by
  sorry

end FilmusIhringer
