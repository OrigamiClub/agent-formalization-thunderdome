# Agent 049 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` whose conclusion is an existential
over an absolute constant `C : ℝ`, followed by a universally quantified statement
over the ambient type, `k`, `r`, and the family `W`. Ends in `:= by sorry`.

Two auxiliary definitions:

* `IsSunflower (petals : Finset (Finset α)) (core : Finset α)` :=
  `(petals : Set (Finset α)).Pairwise (fun S T => S ∩ T = core)`.
  I.e. any two distinct members meet in exactly `core` ("pairwise intersections
  all coincide" phrasing, with the core named explicitly).
* `ContainsSunflower (W : Finset (Finset α)) (r : ℕ)` := there is a subfamily
  `𝒮 ⊆ W` with `𝒮.card = r` that is an `IsSunflower` for some `core`.

## Encoding decisions and why

* **Set representation:** `Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]`. `Finset` gives "finite family" for free and makes `𝒮.card`
  and `S ∩ T` available directly. `DecidableEq` is needed for `∩` on `Finset`.
* **Distinctness:** elements of a `Finset` are automatically distinct, so
  `𝒮.card = r` encodes "`r` distinct sets" without an extra hypothesis. Same
  reason no explicit distinctness clause is needed for `W`.
* **Sunflower predicate:** defined locally rather than assuming a Mathlib name.
  Built on `Set.Pairwise` (a well-established Mathlib identifier). The core is
  given explicitly as a parameter; `ContainsSunflower` existentially quantifies
  it. Petals are *not* required nonempty (matches the classical definition where
  a petal is `S \ core`, possibly empty for at most one member).
* **Constant `C`:** existentially quantified *inside* the theorem but *outside*
  the `∀ {α} ...`, so `C` cannot depend on `α`, `k`, `r`, or `W` — a true
  absolute constant. `0 < C` included.
* **Logarithm:** `Real.log` (natural log). The base only changes `C`, so this is
  faithful to "log k". `k` is coerced `ℕ → ℝ` inside `Real.log`.
* **Cardinality:** `Finset.card` throughout; the size comparison
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` is done in `ℝ` after coercing
  `W.card`. The exponent `k` is a `ℕ` (monoid power).
* **Degenerate `k`:** hypothesis `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes the
  bound `0`, and `|W| > 0` does not suffice to force `r` pairwise-disjoint
  singletons; Bell–Chueluecha–Warnke state the bound for `k ≥ 2`. `k = 0` is
  likewise excluded. `1 ≤ r` kept (task says "positive integers"); `r = 1` makes
  the conclusion trivial, which is harmless.
* **Cardinality "exactly k":** `∀ S ∈ W, S.card = k`.

## Uncertainties

* Whether current Mathlib already has a sunflower predicate (something like
  `Finset.IsSunflower` / a `Sunflower` namespace, possibly from an
  Erdős–Rado PR). I did not rely on one; if it exists, `IsSunflower` here could
  be replaced by it.
* `Set.Pairwise` signature/argument order is assumed to be
  `Set.Pairwise (s : Set α) (r : α → α → Prop)` — believed correct.
* Auto-bound universe handling for the inner `∀ {α : Type*}` under an outer
  `∃ C` is assumed to elaborate fine (standard pattern for "absolute constant"
  statements).
* The precise polynomial factor in the literature varies (`log k`, `log(rk)`,
  etc.); I used the `(C · r · log k)^k` form given in the task.
