import Mathlib

open Nat

/-!
Glaisher's theorem (independent formalization, agent 13).

Representation choice: rather than using Mathlib's `Nat.Partition` structure,
a partition of `n` is represented directly and explicitly as a
`Multiset ℕ` `s` satisfying:
  * `∀ i ∈ s, 0 < i`   (all parts are positive), and
  * `s.sum = n`        (the parts sum to `n`).

This is the standard "multiset of positive naturals summing to n" encoding
of an (unordered) partition, spelled out inline instead of going through a
bundled structure.

The two families of partitions are then the following `Set (Multiset ℕ)`:

  * `glaisherParts k n`  : partitions of `n` with no part divisible by `k`,
      i.e. `∀ i ∈ s, ¬ (k ∣ i)`;
  * `boundedRepParts k n`: partitions of `n` in which every distinct part
      occurs strictly fewer than `k` times, i.e. `∀ i ∈ s, s.count i < k`
      (multiplicity of `i` in the multiset `s` is `< k`).

The theorem is stated as an equality of `Set.ncard` (natural-number
cardinalities of these sets), rather than as an explicit bijection. Since
both sets are finite (bounded-part-count multisets summing to a fixed `n`
form a finite set), `Set.ncard` faithfully counts them and the equality
`Set.ncard (glaisherParts k n) = Set.ncard (boundedRepParts k n)` is a
faithful transcription of "the two counting functions A_k(n) and B_k(n)
agree for every n". Finiteness itself is not asserted here since it is not
needed to *state* the theorem; only the counts are asserted equal.

The hypothesis `k ≥ 2` is required (Glaisher's theorem is stated for
k ≥ 2; k = 2 recovers Euler's odd/distinct-parts theorem).
-/

/-- The set of partitions of `n` (as multisets of positive naturals summing
to `n`) none of whose parts is divisible by `k`. -/
def glaisherParts (k n : ℕ) : Set (Multiset ℕ) :=
  {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, ¬ (k ∣ i)}

/-- The set of partitions of `n` (as multisets of positive naturals summing
to `n`) in which every part occurs strictly fewer than `k` times (no part
is repeated `k` or more times). -/
def boundedRepParts (k n : ℕ) : Set (Multiset ℕ) :=
  {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, s.count i < k}

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every natural number `n`, the
number of partitions of `n` into parts none of which is divisible by `k`
equals the number of partitions of `n` in which every part occurs fewer
than `k` times. (The case `k = 2` is Euler's theorem: partitions into odd
parts are equinumerous with partitions into distinct parts.) -/
theorem glaisher_agent13 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (glaisherParts k n).ncard = (boundedRepParts k n).ncard := by
  sorry
