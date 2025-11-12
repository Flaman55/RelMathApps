# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki

from typing import List

# -------------------------------------------------------------
#  STRUCTURAL SPACE  S^S·U
# -------------------------------------------------------------
#  In this relational framework, each structural element S 
#  generates its own dimension of existence (S^S), 
#  while the factor U defines the cognitive grid — 
#  the minimal unit of translation between structure and value.
#
#  U = 1  → fully relational (pure) space.
#  U > 1  → "densified" structure requiring conversion 
#            to manifest in our additive (value-based) space.
# -------------------------------------------------------------


def shift_cycle_down(cycle: List[int]) -> List[int]:
    """Shift a binary structural cycle by one step — 
    simulating the self-movement of S along its own axis."""
    return cycle[1:] + [cycle[0]]


def structural_cycle_S_to_S_U(S: int, U: int) -> List[int]:
    """
    Generate a relational cycle for the structural space S^S·U.

    Each cycle represents the relational existence of entity S 
    within a structure whose full relational extension equals S^S * U.
    """
    base = [1] + [0] * (S - 1)
    return base * (S ** S * U // S)  # full relational length: S^S·U


def visualize_cycle(cycle: List[int]) -> str:
    """Simple visualization of a binary cycle as a structural symbol."""
    return ''.join('█' if x == 1 else '·' for x in cycle)


# -------------------------------------------------------------
#  GENERATING PRIMALITY IN THE SPACE S^S·U
# -------------------------------------------------------------
#  Here, primality is defined as a state of relational independence:
#  a new element S is admitted only if none of the existing cycles 
#  is currently active (i.e., has '1' at the front).
#
#  This corresponds to a structural state that does not interfere 
#  with any previously established cycles.
# -------------------------------------------------------------


def relational_primality_S_to_S_U(limit: int, U: int = 2) -> List[int]:
    primes = []     # list of detected "relational primalities"
    cycles: List[List[int]] = []

    for S in range(2, limit + 1):
        # --- Update existing cycles (movement in relational space)
        status = []
        for i in range(len(cycles)):
            cycles[i] = shift_cycle_down(cycles[i])
            status.append(cycles[i][0] == 1)

        # --- Identify a new relational prime
        if not any(status):
            primes.append(S)

            # Generate structural cycle in the S^S·U space
            new_cycle = structural_cycle_S_to_S_U(S, U)
            rel_length = len(new_cycle)        # relational length: S^S * U

            # ---------------------------------------------------------
            #  CONVERSION TO VALUE SPACE (OUR DOMAIN)
            # ---------------------------------------------------------
            #  Step 1: Normalize the cognitive grid to our unit system.
            #          Divide by U since our space assumes U=1.
            normalized_length = rel_length / U     # S^S
            #  Step 2: Project onto the value axis through the S-root.
            #          This translates from relational to additive space.
            value = normalized_length ** (1 / S)   # numerical projection
            # ---------------------------------------------------------

            print(f"Step={S} → relational length S^S·U = {rel_length:.0f}, "
                  f"after /U = {normalized_length:.0f}, "
                  f"value projection = {value:.6g}")

            cycles.append(new_cycle)

    return primes


# -------------------------------------------------------------
#  OPERATIONAL LAYER
# -------------------------------------------------------------
#  This is where classical prime numbers appear as manifestations
#  of relational primality after converting S^S·U space
#  into our standard U=1 grid.
# -------------------------------------------------------------

if __name__ == "__main__":
    result = relational_primality_S_to_S_U(10, U=2)
    print("\nEmergent primes in S^S·U space:", result)
    print("Number of emergent primes:", len(result))


# -------------------------------------------------------------
#  STRUCTURAL COMMENTARY
# -------------------------------------------------------------
#  This algorithm does not compute numbers — it recreates 
#  the motion of relations within a space where "value" 
#  does not exist independently but emerges through conversion.
#
#  S^S represents a self-referential structure, devoid of quantity.
#  kS is its projection into our additive realm, 
#  where "more" and "less" become meaningful.
#
#  U is not a value but a *cognitive unit* — 
#  the definition of minimal distinguishable distance, 
#  the principle that makes “different” measurable.
#
#  In this interpretation, prime numbers are manifestations 
#  of pure structural independence. 
#  After conversion from S^S·U to U=1, they appear as 2, 3, 5, 7, …
#
#  The code does not generate numbers — it models the moment 
#  when structural motion becomes visible to us as numerical form.
# -------------------------------------------------------------
