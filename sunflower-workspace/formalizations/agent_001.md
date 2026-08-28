# agent_001 — improved sunflower lemma (statement only)

## Form chosen

Single existential over an absolute constant `C : ℝ` with `0 < C`, then a universally
quantified implication:

> for every ambient type `α` with `DecidableEq`, every positive `k, r : ℕ`, and every
> `W : Finset (Finset α)` whose members all have card `k`, if
> `(W.card : ℝ) > (C * r * Real.log (k + 1)) ^ k` then there exist `core : Finset α` and
> `petals ⊆ W` with `IsSunflower r core petals`.

`IsSunflower r core petals` is a local definition: `petals.card = r` together with
"pairwise intersections of distinct members equal `core`".

## Encoding decisions and why

- **Set family = `Finset (Finset α)` over an arbitrary type `α`.** Gives finiteness of `W`
  for free, makes the `r` sunflower members automatically distinct, and lets `|W|` be
  `Finset.card`. Distinctness of members therefore needs no separate hypothesis. Alternatives
  considered: `Set (Set α)` + `Set.Finite`, or an injective indexed family `Fin r → Finset α`
  for the petals; the Finset subfamily `petals ⊆ W` is the lightest.
- **Sunflower predicate.** No sunflower lemma or `IsSunflower`/`Sunflower` predicate exists in
  the Mathlib checkout consulted (commit `520045a`, 2026-07-23; `grep -ri sunflower` over
  `Mathlib/` returns nothing). So `IsSunflower` is defined here. I used the compact
  "all pairwise intersections coincide" form rather than spelling out `core ⊆ s` and
  petal-disjointness, since for `r ≥ 2` the compact form implies both. `r` is a parameter of
  the predicate, fixed via `petals.card = r`.
- **`r ≥ 2` NOT baked into `IsSunflower`.** The main theorem ranges over `r ≥ 1`; baking
  `2 ≤ r` in would make the `r = 1` conclusion unprovable. For `r ≤ 1` the intersection
  clause is vacuous and a sunflower trivially exists once `W` is nonempty (which the bound
  forces), so the statement stays consistent.
- **Logarithm = `Real.log` (natural log).** The constant `C` absorbs the choice of base.
- **`k = 1` / `k = 0` handling.** `log` is applied to `k + 1`, not `k`. With `Real.log k` the
  RHS is `0` at `k = 1`, which would (falsely) claim any nonempty family of singletons has an
  `r`-sunflower for every `r`. Using `Real.log (k + 1)` keeps the RHS positive and the
  statement true for all positive `k`, and for `k ≥ 2` differs from `Real.log k` only through
  the value of the absolute constant. `k = 0` is excluded by `1 ≤ k` (and is degenerate: all
  members equal `∅`, so `W.card ≤ 1`). An equally defensible alternative is to keep
  `Real.log k` and instead require `2 ≤ k`.
- **`C` existentially quantified, placed before the `∀ {α} ..`** so it cannot depend on the
  ambient type / `k` / `r` — i.e. a true absolute constant. Chose `0 < C` rather than
  `1 ≤ C`; the intended witness is large anyway.
- **Cardinality comparison in `ℝ`.** `(W.card : ℝ) > (…)^k`, with `k : ℕ` as the exponent
  (monoid power). `r` and `k` are coerced explicitly (`(r : ℝ)`, `(k : ℝ)`).

## Uncertainties

- Whether `∀ {α : Type*} [DecidableEq α] …` nested under `∃ C` elaborates cleanly as written
  (implicit + instance binders inside a `∀` in a Prop). I believe it does; if not, the fix is
  to make `α`, and the instance, explicit or to move `C` in as a leading hypothesis
  `(C : ℝ) (hC : 0 < C)` with a section `variable`.
- No compiler was available; identifiers `Real.log`, `Finset.card`, `Finset` intersection
  (`s ∩ t`, needs `[DecidableEq α]`), and `⊆` on `Finset (Finset α)` are from memory but
  standard.
- My prior recollection of a `Finset.IsSunflower` in Mathlib could not be confirmed and
  appears to be absent in this version; treated as not existing.
- Faithfulness caveat: `Real.log (k+1)` in place of `log k` is a deliberate, constant-only
  deviation to repair `k = 1`.
