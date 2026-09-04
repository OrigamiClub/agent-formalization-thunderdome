import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:
* the forward direction (`k ≥ 2d`): a uniform junta bound `m(d)`;
* the converse direction (`1 ≤ k < 2d`): the junta size cannot be bounded;
* an explicit witnessing family for the converse.

See `agent_068.md` for the encoding rationale and the note on the witnessing family.
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of a subset `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- A function on the slice *has degree `≤ d`* if it agrees, at every point of the slice,
with the evaluation at the indicator vector of some real multivariate polynomial of
total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ x : Slice n k, f x = MvPolynomial.eval (indicator x.1) p

/-- A function on the slice is an *`m`-junta* if there is a set `J` of at most `m`
coordinates such that the value at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ x y : Slice n k, x.1 ∩ J = y.1 ∩ J → f x = f y

/-- Block `i` (intended range `1 ≤ i ≤ ℓ`): the `e` coordinates `{(i-1)·e, …, i·e - 1}`
of `Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => (i - 1) * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e)

/-- The explicit witnessing family: the OR of `ℓ` disjoint conjunctions ("blocks") of
`e` coordinates each, `S ↦ [∃ i ≤ ℓ, block i ⊆ S]`.

With `e = min d k` and `1 ≤ k < 2d` one has `e > k/2`, hence no two disjoint blocks
fit simultaneously in a `k`-set; therefore on the slice this function coincides with
the multilinear polynomial `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` and is Boolean of
degree `e ≤ d`.  (The prose of the theorem writes `∏_i (∑_j x)`; that real polynomial
is not `{0,1}`-valued on the slice, so we take the `∑_i ∏_j x` reading — see the note.) -/
open Classical in
noncomputable def addrFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => if (∃ i, 1 ≤ i ∧ i ≤ ℓ ∧ block n e i ⊆ S.1) then 1 else 0

/-! ## Forward direction (`k ≥ 2d`) -/

/-- **Filmus–Ihringer, positive part.**  There is a function `m : ℕ → ℕ` such that for
every `d ≥ 1`: if `k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d` function
on the slice `binom([n],k)` is an `m(d)`-junta. -/
theorem boolean_degree_junta_of_ge :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f (m d) := by
  sorry

/-! ## Converse direction (`1 ≤ k < 2d`) -/

/-- **Filmus–Ihringer, converse part.**  If `1 ≤ k < 2d` then for every `m` there exist
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem not_bounded_junta_of_lt
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnesses for the converse.**  With `e = min d k` and `1 ≤ k < 2d`, and
for `n ≥ 2ℓe` (and `n ≥ 2k`), the OR-of-`ℓ`-blocks function `addrFun n k e ℓ` on
`binom([n],k)` is Boolean, has degree `≤ d`, and is not an `m`-junta for any `m < ℓe`.
Taking `ℓ` arbitrarily large yields `not_bounded_junta_of_lt`. -/
theorem addrFun_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e ℓ n : ℕ) (he : e = min d k) (hℓ : 2 * ℓ * e ≤ n) (hk : 2 * k ≤ n) :
    IsBoolean (addrFun n k e ℓ) ∧
    HasDegreeLE (addrFun n k e ℓ) d ∧
    ∀ m : ℕ, m < ℓ * e → ¬ IsJunta (addrFun n k e ℓ) m := by
  sorry

end FilmusIhringer
