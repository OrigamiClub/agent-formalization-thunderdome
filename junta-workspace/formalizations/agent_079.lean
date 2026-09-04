import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Three theorems, all closed with `sorry`:

* `filmus_ihringer_forward`          — the positive direction (`k ≥ 2d` ⇒ junta);
* `filmus_ihringer_converse`         — sharpness of `k ≥ 2d` (clean existential form);
* `filmus_ihringer_converse_explicit`— the same sharpness, witnessed by an explicit
  family `gFamily`.

See `agent_079.md` for the encoding rationale and the (few) uncertain identifiers.
-/

/-- The `k`-slice `binom([n], k)`: subsets `S ⊆ {0, …, n-1}` with `|S| = k`,
encoded as a subtype of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolValued {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- Characteristic vector in `ℝ^n` of a subset `S : Finset (Fin n)`. -/
def charVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f : Slice n k → ℝ` has *degree `≤ d`* if it agrees, everywhere on the slice, with
the evaluation at characteristic vectors of some real polynomial of total degree `≤ d`.
(Multilinearity is irrelevant here: evaluation happens only at `0/1` points.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (charVec S.1) p

/-- `f : Slice n k → ℝ` is an *`m`-junta* if there is a set `J` of at most `m`
coordinates such that the value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a bound `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`≤ d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolValued f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, sharpness of the `k ≥ 2d` hypothesis.**
If `1 ≤ k < 2d` then the junta bound fails completely: for every `m` there are `n ≥ 2k`
and a Boolean degree-`≤ d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolValued f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit tightness family.  With `e = min d k`, split the first `ℓ·e`
coordinates into `ℓ` consecutive blocks of size `e` (block `i` is `{i·e, …, i·e+e-1}`).
`gFamily n k d ℓ` sends `S` to `∑_{i<ℓ} ∏_{j<e} [ (i·e + j) ∈ S ]`, i.e. the number of
blocks entirely contained in `S`.  Once `k < 2d` and `e = min d k`, no two disjoint
`e`-blocks both fit inside a `k`-set, so on the slice this sum is `0`/`1`-valued and
equals the indicator "some block ⊆ S". -/
def gFamily (n k d ℓ : ℕ) : Slice n k → ℝ :=
  fun S =>
    ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range (min d k),
      (if i * min d k + j ∈ S.1.map Fin.valEmbedding then (1 : ℝ) else 0)

/-- **Filmus–Ihringer, explicit witnesses.**
For `1 ≤ k < 2d` and every `ℓ ≥ 1`, once `n ≥ 2·ℓ·min d k` the function
`gFamily n k d ℓ` is Boolean, has degree `≤ d` on the slice, and is not an `m`-junta
for any `m < ℓ·min d k`.  Letting `ℓ → ∞` defeats every fixed junta bound, which yields
`filmus_ihringer_converse`. -/
theorem filmus_ihringer_converse_explicit (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 2 * ℓ * min d k ≤ n) :
    IsBoolValued (gFamily n k d ℓ) ∧
    HasDegreeLE (gFamily n k d ℓ) d ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (gFamily n k d ℓ) m) := by
  sorry
