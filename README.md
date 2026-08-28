# agent-formalization-thunderdome

Independent-agent formalization diversity studies: for a given theorem, spawn N
context-isolated agents (N = 20 or 100 so far), have each independently produce a
Lean 4 formalization of the statement (no coordination, no proof required —
`:= by sorry`), then compare the results for equivalence by (1) bridging —
arguing/proving that differently shaped formalizations assert the same thing, and
(2) a lexicographic "looks-good-enough" check — clustering formalizations that are
textually identical after normalization. The 20-agent runs were additionally
**compiled** against a live Lean/Mathlib checkout (`leanprover/lean4:v4.29.0-rc3`,
Mathlib commit `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`) to verify both the
formalizations and the hand-argued bridge claims. The 100-agent run is
formalization-only: no comparison component, and the files were not compiled.

## Results

### [`gvb-workspace/`](gvb-workspace) — Gilbert–Varshamov bound

- **Low diversity**: all 20 agents converged on the same combinatorial/existential
  form (alphabet `Fin q`, codewords `Fin n → Fin q`, code as `Finset`), differing
  only in cosmetic notation — likely because the prompt spelled the inequality out
  explicitly. One true equivalence class.
- **Compiled**: **18/20 PASS**. Agents 11 and 19 **fail to parse** — they used the
  legacy `∑ i in s` sum-binder syntax, which this Mathlib revision rejects (needs
  `∑ i ∈ s`). A real defect the hand-argument alone didn't catch.
- All Tier-1 (definitional) bridge claims compile via `rfl`.
- Details: [`gvb-workspace/comparison/REPORT.md`](gvb-workspace/comparison/REPORT.md),
  [`gvb_equivalence.csv`](gvb-workspace/comparison/gvb_equivalence.csv),
  [`bridges.lean`](gvb-workspace/comparison/bridges.lean).

### [`glaisher-workspace/`](glaisher-workspace) — Glaisher's theorem

- **Real structural diversity** across three independent axes: partition
  representation (`Nat.Partition n` vs. a raw `Multiset ℕ` predicate defined from
  scratch), cardinality mechanism (`Nat.card` / `Set.ncard` / `Finset.card`), and
  quantifier scope on the multiplicity condition (`∀i∈parts` vs. `∀i`) — 6 distinct
  lexicographic groups.
- All 6 groups bridge to one equivalence class via three escalating tiers: pure
  notation (`rfl`), a short standard lemma (e.g. `Fintype.card_subtype`,
  `Multiset.count_eq_zero_of_notMem`), or a small explicit `Equiv` construction
  (`Nat.Partition n ≃ {s : Multiset ℕ // (∀i∈s,0<i) ∧ s.sum=n}`, since
  `Nat.Partition` is literally that structure under the hood).
- **Compiled**: **20/20 PASS**, and every bridge tier was written as a real proof
  and compiled successfully — including catching and fixing one wrong guessed
  lemma name (`count_eq_zero_of_not_mem` → the real name is
  `count_eq_zero_of_notMem`) via the compiler rather than documentation lookup.
- Details: [`glaisher-workspace/comparison/REPORT.md`](glaisher-workspace/comparison/REPORT.md),
  [`glaisher_equivalence.csv`](glaisher-workspace/comparison/glaisher_equivalence.csv),
  [`bridges.lean`](glaisher-workspace/comparison/bridges.lean).

### [`sunflower-workspace/`](sunflower-workspace) — improved sunflower lemma (log bound)

- **100 agents**, formalization-only (no bridging, not compiled). Target: the
  Alweiss–Lovett–Wu–Zhang / Rao / Bell–Chueluecha–Warnke bound
  `f(k,r) ≤ (C·r·log k)^k`.
- **Very low diversity**, like GVB: **100/100** used `W : Finset (Finset α)` over
  an ambient `[DecidableEq α]`, `Finset.card`, `Real.log` (natural log), an
  outermost `∃ C : ℝ, 0 < C`, a locally-defined core-based sunflower predicate,
  and no nonempty-petal requirement. Zero used `Real.logb 2`, `Nat.log`,
  `Set.ncard`, or a `Set`-with-finiteness representation.
- The one axis with a real modelling decision — the `k ≤ 1` degeneracy of
  `(C·r·log k)^k` (`log 1 = 0` makes the bound false, since `f(1,r) = r`) — split
  **73 / 27**: exclude it with a `2 ≤ k` hypothesis, vs. keep `0 < k` and patch the
  logarithm (`Real.log (k+1)`, 18; `max 1 (Real.log k)`, 9). Other differences
  (explicit `∀∀` vs. `Set.Pairwise` core condition, redundant `Y ⊆ member` clause,
  where `𝒮.card = r` lives, a second `f(k,r)` restatement in 72 files) are
  cosmetic.
- Details: [`sunflower-workspace/REPORT.md`](sunflower-workspace/REPORT.md),
  [`sunflower-workspace/PROMPT.md`](sunflower-workspace/PROMPT.md).

## Takeaway

No agent, in any run, formalized a mathematically wrong statement. The runs differ
mainly in how much genuine diversity the prompt left room for: GVB and the
sunflower run spelled the bound out symbolically and got near-total convergence
(one true equivalence class / one shared skeleton), while Glaisher's leaner prompt
produced real structural diversity across 6 groups. Where compilation was run
(the 20-agent runs) it caught real issues pure inspection missed — a syntax
incompatibility in 2/20 GVB files, and a wrong lemma name during bridge-writing.
