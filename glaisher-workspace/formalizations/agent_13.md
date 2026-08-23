# Glaisher's theorem — formalization notes (agent 13)

**Partition representation.** A partition of `n` is represented directly (not via Mathlib's `Nat.Partition` structure) as a `Multiset ℕ`, `s`, satisfying `∀ i ∈ s, 0 < i` (positive parts) and `s.sum = n` (parts sum to `n`); this pair of side conditions is written inline as part of each set-builder definition rather than bundled into a structure.

**Encoding the two conditions.** "No part divisible by `k`" is `∀ i ∈ s, ¬ (k ∣ i)`, packaged as the set `glaisherParts k n`. "Every part occurs fewer than `k` times" is `∀ i ∈ s, s.count i < k`, using `Multiset.count` to get the multiplicity of each part `i` within `s`; this is packaged as `boundedRepParts k n`.

**Statement form.** I stated the theorem as a cardinality equality, `(glaisherParts k n).ncard = (boundedRepParts k n).ncard`, using `Set.ncard` (natural-number set cardinality, defaulting to `0` on infinite sets) applied directly to `Set (Multiset ℕ)`, rather than going through `Fintype`/`Nat.card` of a subtype or asserting an explicit bijection.

**Choices/simplifications.** I did not assert finiteness of the two sets explicitly (not needed to state the equality, though it is true and would be needed for a real proof). The hypothesis `k ≥ 2` is included since the theorem is only meaningful/true for `k ≥ 2` (and `k = 2` is exactly Euler's odd-parts/distinct-parts theorem). I deliberately avoided Mathlib's `Nat.Partition` structure and used raw multisets instead, and used `Set.ncard` instead of `Nat.card` on subtypes, as an independent encoding choice for this diversity study.
