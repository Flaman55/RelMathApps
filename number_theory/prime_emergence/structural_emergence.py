# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki

"""
Prime Emergence — Structural Space Simulation
Part of the Relational Mathematics Framework
https://relationalmathematics.org/

Description:
-------------
This module simulates the structural evolution of relational space,
where arithmetic values are replaced by symbolic cycles and resonance states.
No numeric arithmetic is performed — instead, the system evolves through 
symbolic relations that emulate the emergence of prime-like irreducible states.

Concepts:
----------
U — Grid constant (defines the minimal distance between structural points)
S — Structural iteration step (resonance order or cycle length)
Cycles — Represent evolving relational clusters in structural space
"""

import random
import time


# ============================================================
# Symbol Generation
# ============================================================

def get_symbol_sets(variant: int = 1):
    """
    Return symbol pools and choice sets for a selected visual variant.
    Variants:
        1 - Formal (default)
        2 - Runic
        3 - Geometric
    """
    if variant == 2:
        # --- Variant 2: Runic ---
        SYMBOL_POOL = [
            "ᚠ","ᚢ","ᚦ","ᚨ","ᚱ","ᚲ","ᚷ","ᚹ","ᚺ","ᚾ",
            "ᛁ","ᛃ","ᛇ","ᛈ","ᛉ","ᛋ","ᛏ","ᛒ","ᛖ","ᛗ",
            "ᛚ","ᛜ","ᛞ","ᛟ","ᛠ","ᚪ","ᚫ","ᚬ","ᚭ","ᚮ",
            "ᚯ","ᚰ","ᚱ","ᚲ","ᚳ","ᚴ","ᚵ","ᚶ","ᚷ","ᚸ",
            "ᚹ","ᚺ","ᚻ","ᚼ","ᚽ","ᚾ","ᚿ","ᛀ","ᛁ","ᛂ"
        ]
        CHOICES = [
            "ᛃ","ᛇ","ᛈ","ᛉ","ᛋ","ᛏ","ᛒ","ᛖ","ᛗ","ᛚ",
            "ᛜ","ᛞ","ᛟ","ᛠ","ᚪ","ᚫ","ᚬ","ᚭ","ᚮ","ᚯ",
            "ᚰ","ᚱ","ᚲ","ᚳ","ᚴ","ᚵ","ᚶ","ᚷ","ᚸ","ᚹ",
            "ᚺ","ᚻ","ᚼ","ᚽ","ᚾ","ᚿ","ᛀ","ᛁ","ᛂ","ᛃ",
            "ᛇ","ᛈ","ᛉ","ᛋ","ᛏ","ᛒ","ᛖ","ᛗ","ᛚ","ᛜ"
        ]

    elif variant == 3:
        # --- Variant 3: Geometric ---
        SYMBOL_POOL = [
            "◯","◇","⬡","⬢","⬣","⬤","◈","◉","◍","◎",
            "◬","◭","◮","◯","◰","◱","◲","◳","◴","◵",
            "◶","◷","◸","◹","◺","◻","◼","◽","◾","◿",
            "⬟","⬠","⬤","⬩","⬪","⬫","⬬","⬭","⬮","⬯",
            "⬰","⬱","⬲","⬳","⬴","⬵","⬶","⬷","⬸","⬹"
        ]
        CHOICES = [
            "◖","◗","◔","◕","◒","◓","◐","◑","◒","◓",
            "◔","◕","◖","◗","◘","◙","◚","◛","◜","◝",
            "◞","◟","◠","◡","◢","◣","◤","◥","◦","●",
            "◌","◍","◎","◉","◈","◇","◆","□","■","▣",
            "▤","▥","▦","▧","▨","▩","▪","▫","▭","▮"
        ]

    else:
        # --- Variant 1: Formal (default) ---
        SYMBOL_POOL = [
            "⊚","⊛","⊡","⊟","⊠","⊙","⊗","⊘","⊜","⊝",
            "⋄","⋆","⋇","⋈","⋉","⋊","⋋","⋌","⋍","⋎",
            "⋏","⋐","⋑","⋒","⋓","⋔","⋕","⋖","⋗","⋘",
            "⋙","⋚","⋛","⋜","⋝","⋞","⋟","⋠","⋡","⋢",
            "⋣","⋤","⋥","⋦","⋧","⋨","⋩","⋪","⋫","⋬"
        ]
        CHOICES = [
            "α","β","γ","δ","ε","ζ","η","θ","ι","κ",
            "λ","μ","ν","ξ","ο","π","ρ","σ","τ","υ",
            "φ","χ","ψ","ω","ϕ","ϖ","ϱ","ς","ϰ","ϑ",
            "ϕ̇","ϕ̈","φ′","φ″","ψ̇","ψ̈","ξ′","ξ″","η′","η″",
            "ρ̇","ρ̈","σ̇","σ̈","π̇","π̈","μ′","μ″","ν′","ν″"
        ]

    return SYMBOL_POOL[:50], CHOICES[:70]


# ============================================================
# Structural Dynamics
# ============================================================

def step_from_latency_ms(ms_last_digit: int) -> int:
    """Map the last digit of measured latency to a structural step size (S)."""
    if ms_last_digit == 0:
        return 10
    if ms_last_digit in (1, 2):
        return 3
    return ms_last_digit


def choose_unique_marker(used_markers, avoid=None):
    """Select a new unique symbol to mark a newly formed cycle."""
    candidates = [s for s in SYMBOL_POOL if s not in used_markers and s != avoid]
    if not candidates:
        candidates = [s for s in SYMBOL_POOL if s != avoid] or SYMBOL_POOL[:]
    return random.choice(candidates)


def build_frozen_batches(max_n: int):
    """Generate a static set of base symbols representing frozen resonance states."""
    return [random.choice(CHOICES) for _ in range(max_n)]


def prepare_states(max_n: int, S: int):
    """
    Create the sequence of structural states.
    Each state represents an iteration in which new cycles may form or stabilize.
    """
    batches = build_frozen_batches(max_n)
    position = []
    cycles, markers, states = [], [], []

    while len(states) < max_n:
        if len(states) > 0:
            n = random.randint(1, len(states))
        else:
            n = 1

        sym_n = batches[len(states) % len(batches)]
        position.extend([sym_n] * S)

        # Advance all existing cycles
        for i in random.sample(range(len(cycles)), len(cycles)):
            for _ in range(S):
                first = cycles[i].pop(0)
                cycles[i].append(first)

        # Detect resonance collisions
        hits = [i for i in range(len(cycles)) if cycles[i] and cycles[i][0] == markers[i]]
        eliminated = bool(hits)

        # Create a new cycle if no collision occurred
        if not eliminated and len(states) >= 1:
            marker = choose_unique_marker(markers, avoid=sym_n)
            new_cycle_length = (len(states) + 1) * S
            new_cycle = [marker] + [sym_n] * (new_cycle_length - 1)
            cycles.append(new_cycle)
            markers.append(marker)

        fronts = [c[0] for c in cycles if c]
        coherent = (not eliminated) and (len(fronts) == len(set(fronts)))

        states.append((
            n, position.copy(), [c.copy() for c in cycles],
            markers.copy(), hits.copy(), coherent, S, sym_n
        ))

    return states


# ============================================================
# Display and Analysis
# ============================================================

def show_terminal(states):
    """Display the progression of cycles and resonances in the terminal."""
    prev_cycle_count = 0

    for (n, position, cycles, markers, hits, coherent, S, sym_n) in states:
        t_prime = time_map(n)
        print(f"\n--- Step {t_prime} | Batch Symbol = {sym_n} ---")

        current_count = len(cycles)

        if current_count > prev_cycle_count:
            new_cycle = cycles[-1]
            idx = current_count
            count = len(new_cycle)
            display = ''.join(new_cycle[:5]) + f" ({count})" if count > 5 else ''.join(new_cycle) + f" ({count})"
            print("Cycles:")
            print(f"  cycle {idx:>2}: {display}")

        if hits:
            print("⚡ Cycle collisions detected")
        elif coherent:
            print("🌐 Full synchronization: no collisions.")
        else:
            print("✅ Stable resonance: no collisions, new cycle formed.")

        prev_cycle_count = current_count

    print("\n=== FINAL SUMMARY ===")
    if not states:
        print("No states generated.")
        return

    last_cycles = states[-1][2]
    print("Cycles:")
    for idx, cycle in enumerate(last_cycles, start=1):
        count = len(cycle) // S
        display = ''.join(cycle[:5]) + f" ({count})" if count > 5 else ''.join(cycle) + f" ({count})"
        print(f"  cycle {idx:>2}: {display}")


# ============================================================
# Temporal Mapping
# ============================================================

def time_map(n: int) -> int:
    """Nonlinear mapping of iteration index to display time."""
    return int(5 * (n ** 0.5)) + n


# ============================================================
# Main Execution
# ============================================================

def run():
    """Interactive entry point for the simulation."""
    t0 = time.perf_counter()

    try:
        max_n = int(input("Enter number of structural steps (e.g. 20): ").strip())
    except ValueError:
        print("Invalid number. Exiting.")
        return

    if max_n < 2:
        print("Minimum is 2. Exiting.")
        return
    if max_n > 1000:
        print("Maximum is 1000. Exiting.")
        return

    elapsed_ms = int((time.perf_counter() - t0) * 1000)
    S = step_from_latency_ms(elapsed_ms % 10)

    # Initialize symbolic environment
    global SYMBOL_POOL, CHOICES
    SYMBOL_POOL, CHOICES = get_symbol_sets(variant=1)

    states = prepare_states(max_n, S)
    show_terminal(states)


if __name__ == "__main__":
    run()
