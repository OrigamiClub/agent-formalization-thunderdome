import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Nothing is proved: every theorem ends in `:= by sorry`.

We formalize:

* `filmus_ihringer_forward`      — the positive direction (`k ≥ 2d ⇒` bounded junta);
* `filmus_ihringer_converse`     — the negative direction, as a pure existential;
* `filmus_ihringer_tightness_family` — the negative direction with the explicit
  witnessing family `∏_{i<ℓ} (∑_{j<e} x_{i·e+j})`, `e = min d k`, transcribed literally.

## Encoding choices

* The slice `binom([n],k)` is `Slice n k := {S : Finset (Fin n) // S.card = k}`.
* Boolean codomain: real-valued functions with `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`.
* "degree ≤ d": there is a real multilinear-or-not `MvPolynomial (Fin n) ℝ` of
  `totalDegree ≤ d` agreeing with `f` on the slice at the 0/1 indicator vector
  `slicePoint S i = if i ∈ S then 1 else 0`.
* "m-junta": there is `J : Finset (Fin n)` with `J.card ≤ m` such that `f S` depends
  only on `S ∩ J`.
* `m(d)` is an existential *inside* the forward statement (one `∃ m : ℕ` per `d`).
-/

open scoped BigOperators

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The 0/1 indicator vector of a slice point, as an evaluation point in `ℝ^n`. -/
def slicePoint {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* on the slice: it agrees on the slice with a real polynomial
of total degree `≤ d`, evaluated at the 0/1 indicator vector. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (slicePoint S) p

/-- `f` is an *m-junta*: its value depends only on `S ∩ J` for some coordinate set
`J` of size `≤ m`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`≤ d` function on `binom([n],k)` is an `m`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ (k n : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse (Filmus–Ihringer), existential form.**
If `1 ≤ k < 2d` then no uniform junta bound holds: for every `m` there are `n ≥ 2k`
and a Boolean degree-`≤ d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witnessing family, transcribed literally:
`familyFun d k n ℓ  S  =  ∏_{i < ℓ} ( ∑_{j < e}  x_{i·e + j}(S) )`,  with `e = min d k`,
where `x_t(S)` is `1` if `S` contains the coordinate with index `t`, else `0`.

Here `∑_{j < e} x_{i·e+j}(S)` is realized as the number of elements of `S` whose
underlying index in `ℕ` lies in the `i`-th block `{i·e, …, i·e + e - 1}`. -/
noncomputable def familyFun (d k n ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∏ i ∈ Finset.range ℓ,
    ∑ j ∈ Finset.range (min d k),
      ((S.val.filter (fun a => (a : ℕ) = i * min d k + j)).card : ℝ)

/-- **Converse (Filmus–Ihringer), explicit family.**
For `1 ≤ k < 2d`, `e = min d k`, and any `ℓ ≥ 1`, whenever `n ≥ 2·ℓ·e` (and `n ≥ 2k`)
the function `familyFun d k n ℓ = ∏_{i<ℓ}(∑_{j<e} x_{i·e+j})` is a Boolean
degree-`≤ d` function on `binom([n],k)` that is not an `(ℓ·e)`-junta.
Letting `ℓ → ∞` defeats every fixed junta bound. -/
theorem filmus_ihringer_tightness_family
    (d k ℓ n : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) (hℓ : 1 ≤ ℓ)
    (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n) :
    IsBoolean (familyFun d k n ℓ) ∧
    HasSliceDegreeLE d (familyFun d k n ℓ) ∧
    ¬ IsJunta (ℓ * min d k) (familyFun d k n ℓ) := by
  sorry
