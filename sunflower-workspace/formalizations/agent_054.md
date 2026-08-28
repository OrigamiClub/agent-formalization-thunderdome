# agent_054 — improved sunflower lemma (statement only)

## Form chosen

One theorem `improved_sunflower_lemma` of the shape
`∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k → ∀ W, (∀ s ∈ W, s.card = k) → (C * r * Real.log k)^k < W.card → ∃ F ⊆ W, ∃ Y, IsSunflower r Y F`.

Auxiliary definition `IsSunflower r Y F := F.card = r ∧ (F : Set (Finset α)).Pairwise (fun A B => A ∩ B = Y)`.

## Encoding decisions

- **Set representation**: `Finset α` for the sets, `W : Finset (Finset α)` for the
  family, over an arbitrary ambient type `α` with `[DecidableEq α]` (needed for
  `∩` on `Finset`). No finiteness side-conditions required; distinctness of the
  members of `W` and of a sunflower subfamily `F` is automatic for `Finset`.
- **Sunflower predicate**: defined locally as "exactly `r` sets, pairwise
  intersection constantly `Y`" via `Set.Pairwise`. `Set.Pairwise` quantifies over
  distinct pairs, so it gives the `S_i ∩ S_j = Y` for `i ≠ j` condition directly.
  The "every element in ≥ 2 sets is in all" / "petals pairwise disjoint"
  reformulations are equivalent consequences, so not stated. Petals are **not**
  required nonempty (standard; at most one member can equal the core).
- **Petal count**: bundled into the predicate as `F.card = r` using
  `Finset.card`. "Contains a sunflower" is `∃ F ⊆ W, ∃ Y, IsSunflower r Y F`.
- **Cardinality of members**: `∀ s ∈ W, s.card = k` (exactly `k`).
- **Constant `C`**: existentially quantified at the outermost position, with `α`
  quantified *inside*, so `C` is genuinely absolute (independent of `α`, `k`,
  `r`, `W`). Positivity `0 < C` included.
- **Logarithm**: `Real.log` (natural log), with `(k : ℝ)` coercion. Base is
  irrelevant up to rescaling `C`.
- **`k = 0 / k = 1`**: excluded by hypothesis `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0` would make the RHS `0` and the statement false (a single
  singleton does not contain an `r`-petal sunflower for `r ≥ 2`). Noted in the
  docstring that `max (Real.log k) 1` is the alternative that keeps `k = 1`.
- **Threshold**: strict `<` on `W.card` ("more than `(C r log k)^k`").
- **`r`**: `1 ≤ r` (positive integer).

## Uncertainties / guessed identifiers

- `import Mathlib` (blanket) for self-containment.
- Mathlib is believed to have `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
  with a predicate `Finset.IsSunflower` (pairwise-intersection form) and the
  classical Erdős–Rado bound; exact names/signatures not verified, so a local
  `IsSunflower` is used instead of importing one. If the Mathlib predicate exists
  with signature `IsSunflower (F : Finset (Finset α)) (Y : Finset α)`, this
  statement's `IsSunflower r Y F` corresponds to
  `F.card = r ∧ Finset.IsSunflower F Y`.
- `Set.Pairwise` name and its "distinct pairs" semantics assumed as in current
  Mathlib.
- Placement of an instance binder `[DecidableEq α]` inside a term-level `∀`
  telescope is assumed legal Lean 4 (it is in standard Lean 4 syntax).
- Not compiler-checked (no Lean toolchain available).
