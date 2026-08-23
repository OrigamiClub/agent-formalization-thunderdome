# Glaisher's theorem — formalization notes (agent 16)

I represented "a partition of n" using Mathlib's built-in `Nat.Partition n` structure, which bundles a multiset `parts : Multiset ℕ` with proofs that all parts are positive and that `parts.sum = n`. I relied on this type having a `Fintype` instance in Mathlib (partitions of a fixed `n` are finite), letting me count sub-populations via `Finset.filter` on `Finset.univ` and take `.card`.

The "no part divisible by k" condition is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`. The "each part occurs at most k−1 times" condition is encoded as `∀ i ∈ p.parts, p.parts.count i < k`, using `Multiset.count` to get the multiplicity of a value inside the parts multiset directly (rather than converting to a `Finset` of distinct parts and a separate multiplicity function).

I stated the theorem as a cardinality equality (`Finset.card` of the two filtered sets), rather than constructing an explicit bijection, since that most directly mirrors the "the number of partitions ... equals the number of partitions ..." phrasing of the natural-language statement. I took `k : ℕ` with hypothesis `2 ≤ k` and `n : ℕ` universally quantified, matching "fix k ≥ 2... for every natural number n."

Main uncertainty: I am not 100% certain of the exact name/availability of the `Fintype (Nat.Partition n)` instance in the current Mathlib version, nor of the exact field names `parts`, `parts_pos`, `parts_sum` (these are my best recollection of the `Nat.Partition` API); if the instance or field names differ slightly, only minor adjustments (e.g. supplying `DecidableEq`/`Fintype` explicitly, or using `Set.ncard`/`Nat.card` over the corresponding subtype instead of `Finset.filter`) should be needed to fix the statement.
