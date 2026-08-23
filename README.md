# agent-formalization-thunderdome

Independent-agent formalization diversity studies: for a given theorem, spawn 20
context-isolated agents, have each independently produce a Lean 4 formalization of
the statement (no coordination, no proof required — `:= by sorry`), then compare
the 20 results for equivalence by (1) bridging — arguing/proving that differently
shaped formalizations assert the same thing, and (2) a lexicographic
"looks-good-enough" check — clustering formalizations that are textually identical
after normalization. All results were additionally **compiled** against a live
Lean/Mathlib checkout (`leanprover/lean4:v4.29.0-rc3`, Mathlib commit
`777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`) to verify both the formalizations
themselves and the hand-argued bridge claims.

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

## Takeaway

No agent, in either run, formalized a mathematically wrong statement. The two runs
differ mainly in how much genuine diversity the prompt left room for (GVB's prompt
was more leading), and compilation caught real issues — a syntax incompatibility in
2/20 GVB files, and a wrong lemma name during bridge-writing — that pure inspection
missed.
