import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
/-!
# Defs.lean — Definition 2.1: Complete Generative Prime Base

The fundamental structural axiom: the prime base must contain every prime
between P_min and P_max without exception.

Omitting even one prime makes M non-primorial, breaks φ(M)/M = ∏(1−1/p),
and forces the proof into the heuristic/asymptotic regime.
-/

namespace StructuralBertrand

/-! ## Definition 2.1: Complete Generative Prime Base -/

/--
A `PrimeBase` is a nonempty finite set of primes.
-/
structure PrimeBase where
  /-- The underlying finite set of natural numbers -/
  carrier   : Finset ℕ
  /-- Every element is prime -/
  all_prime : ∀ p ∈ carrier, Nat.Prime p
  /-- The base is nonempty -/
  nonempty  : carrier.Nonempty

/-- The minimal element of a prime base -/
def PrimeBase.pMin (B : PrimeBase) : ℕ :=
  B.carrier.min' B.nonempty

/-- The maximal element of a prime base -/
def PrimeBase.pMax (B : PrimeBase) : ℕ :=
  B.carrier.max' B.nonempty

/--
**Definition 2.1** (Complete Generative Prime Base).

A prime base `B` is *complete* if it contains every prime between `B.pMin`
and `B.pMax` without exception:
  `B.carrier = { p prime | B.pMin ≤ p ≤ B.pMax }`

This is the structural axiom of the proof.  Any base omitting even one prime
`p₀ ∈ (P_min, P_max)` is not a complete generative base; its primorial identity
fails and all subsequent structural arguments break down.
-/
def PrimeBase.isComplete (B : PrimeBase) : Prop :=
  ∀ p : ℕ, Nat.Prime p → B.pMin ≤ p → p ≤ B.pMax → p ∈ B.carrier

/--
The *preceding base* obtained by removing P_max from a complete base.
Used in Zero Force and Weight arguments.
-/
def PrimeBase.prev (B : PrimeBase) : Finset ℕ :=
  B.carrier.erase B.pMax

/-! ## Sieve coverage -/

/--
`SieveCovered P n` — `n` is covered by a sieve with bound `P`.

`n` is covered iff its least prime factor `n.minFac ≤ P`,
i.e., some prime in the base divides `n`.
-/
def SieveCovered (P n : ℕ) : Prop :=
  n.minFac ≤ P

/--
`n` is sieve-covered by base `B` iff `SieveCovered B.pMax n`.
-/
def SieveCoveredBy (B : PrimeBase) (n : ℕ) : Prop :=
  SieveCovered B.pMax n

/--
The *window* of a prime base: the interval `(P_max, P_min · P_max]`.
In the standard setting with `P_min = 2` this is `(P_max, 2 · P_max]`.
-/
def window (P_min P_max : ℕ) : Finset ℕ :=
  (Finset.Ioc P_max (P_min * P_max))

/-! ## Proposition 2.1: Primorial identity -/

/--
The *primorial* of a complete generative base: `M = ∏ p ∈ B.carrier, p`.
Because `B` is complete, every prime factor of `M` appears exactly once,
and `φ(M)/M = ∏_{p ∈ B} (1 − 1/p)` holds exactly by multiplicativity of `φ`.
-/
def PrimeBase.primorial (B : PrimeBase) : ℕ :=
  B.carrier.prod id

theorem PrimeBase.primorial_pos (B : PrimeBase) : 0 < B.primorial := by
  apply Finset.prod_pos
  intro p hp
  exact (B.all_prime p hp).pos

end StructuralBertrand
