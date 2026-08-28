# agent_061 — improved sunflower lemma (statement only)

## Form chosen

One auxiliary definition plus one theorem, both self-contained on top of
`import Mathlib`.

- `IsSunflower (P : Finset (Finset α)) (Y : Finset α) : Prop` :=
  `∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y`.
  Explicit-core formulation of a Δ-system. The petal count is `P.card`.

- `improved_sunflower_lemma`:
  `∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
    ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
        ∃ P ⊆ W, P.card = r ∧ ∃ Y, IsSunflower P Y`.

## Encoding decisions and rationale

- **Set representation:** `Finset (Finset α)` over an ambient `α` with
  `[DecidableEq α]`. This keeps every cardinality a plain `ℕ` (`Finset.card`),
  makes "finite family" automatic, and makes membership/distinctness of the
  petals free: a `Finset` of sets already has distinct elements, so `P.card = r`
  delivers `r` distinct members with no extra hypothesis.

- **"Sunflower with r petals":** a subfamily `P ⊆ W` with `P.card = r` together
  with a witnessed core `Y` such that pairwise intersections of distinct members
  all equal `Y`. I chose the explicit-core version rather than "all pairwise
  intersections coincide" because it reads exactly like the classical
  definition and directly names `Y`. The two are equivalent for `r ≥ 2`.

- **Petals nonempty / core ⊆ members:** not stated as hypotheses; both are
  consequences for `r ≥ 2` (if `S ≠ T` in `P` then `Y = S ∩ T ⊆ S` and, since
  `S ≠ T` while `|S| = |T| = k`, the petal `S \ Y` is nonempty). Left implicit
  to keep the statement minimal.

- **Logarithm:** `Real.log` (natural log). The size comparison is done in `ℝ`
  via `((W.card : ℝ))`, since the right-hand side is real-valued. Any other base
  only rescales the absolute constant `C`, so the choice is immaterial to the
  theorem's content.

- **k = 0 / k = 1 handling:** `k` is assumed positive (`0 < k`), matching the
  phrase "positive integers" verbatim. No `max`/`+1` guard is added to
  `Real.log k`. Note `Real.log 1 = 0`, so at `k = 1` the hypothesis degenerates
  to `0 < |W|` and the conclusion would be false for `r ≥ 2`; the lemma carries
  real content only for `k ≥ 2` (`log k > 0`). A stricter `2 ≤ k` would make the
  statement unconditionally true; I kept `0 < k` to stay faithful to the task's
  wording and flagged the gap here.

- **Constant C:** existentially quantified *inside* the theorem, bundled with
  `0 < C`. This is the "there is an absolute constant" reading. `α`, `k`, `r`,
  `W` are all universally quantified after `C`, so `C` is genuinely absolute
  (independent of the ambient type and of `k, r`).

- **Distinctness of members:** not stated — automatic from `Finset`.

## Uncertainties

- I am not aware of an existing sunflower / Δ-system predicate in Mathlib
  (Mathlib has EKR, LYM, Kleitman, shadows, etc., but no sunflower lemma as far
  as I know at the knowledge cutoff), so `IsSunflower` is defined here. If one
  exists it is likely under `Mathlib.Combinatorics.SetFamily.*`; name guess
  `Finset.IsSunflower` or `SetFamily.Sunflower` — unverified.

- `Real.log` is the correct Mathlib identifier for natural log
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`); high confidence.

- Placing an anonymous instance binder `[DecidableEq α]` and an implicit
  `{α : Type*}` inside the `∀` chain under an `∃ C` is, I believe, accepted in
  Lean 4 / Mathlib term-mode statements; not machine-checked here (no compiler
  available).

- The exact published shape of the bound varies by source
  (`(C r log k)^k`, `(C log(rk))^k`, `(a k log k)^k` after refinement); I used
  the form named in the task, `(C · r · log k)^k`.
