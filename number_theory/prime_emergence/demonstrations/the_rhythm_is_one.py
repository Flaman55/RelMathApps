# The Rythm is one, the numbers are many
import random
import time

SYMBOL_POOL = [
    "🪐","🎈","💫","⚙️","🎲","🛰️","🧩","🪄","🧪","🧭",
    "🗝️","🔮","🧲","🪁","🪅","🪞","🪙","🧬","🧯","🧱",
    "🛡️","⚗️","🧵","🪡","🧷","🧫","🧲","🧲","🧲","🪨",
    "🪤","🧰","🧯","🧲","🪓","🧲","🪃","🧱","🧲","🧲",
    "🪜","🧯","🧲","🧪","🪙","🧭","🧲","🧩","🪄","🛰️"
][:50]  

CHOICES = [
    "🍕","🔥","💧","🦊","🙂","🌟","🍀","🌙","🌊","🌋",
    "🌤️","🍎","🍌","🍇","🍉","🍓","🍒","🥝","🍑","🥑",
    "🥕","🌽","🍄","🥨","🥐","🍪","🍩","🍰","🍫","🍭",
    "🌵","🌼","🌻","🌷","🌸","🌺","🌲","🌳","🍁","🍂",
    "🌧️","⛄","🌈","🌪️","🌊","🔥","🍕","💧","🦊","🌟",
    "🍕","🔥","💧","🦊","🙂","🌟","🍀","🌙","🌊","🌋",
    "🌤️","🍎","🍌","🍇","🍉","🍓","🍒","🥝","🍑","🥑"
]

def step_from_latency_ms(ms_last_digit: int) -> int:
    if ms_last_digit == 0:
        return 10
    if ms_last_digit in (1, 2):
        return 3
    return ms_last_digit

def choose_unique_marker(used_markers, avoid=None):
    cand = [s for s in SYMBOL_POOL if s not in used_markers and s != avoid]
    if not cand:
        cand = [s for s in SYMBOL_POOL if s != avoid] or SYMBOL_POOL[:]
    return random.choice(cand)

def build_frozen_batches(max_n: int):
    return [random.choice(CHOICES) for _ in range(max_n)]

def prepare_states(max_n: int, S: int):
    batches = build_frozen_batches(max_n)
    position = []
    cycles, markers, states = [], [], []
    n = 1

    while len(states) < max_n:
        if len(states) > 0:
            n = random.randint(1, len(states))

        sym_n = batches[len(states) % len(batches)]
        position.extend([sym_n] * S)

        for i in random.sample(range(len(cycles)), len(cycles)):
            L = len(cycles[i])
            if L:
                for _ in range(S):
                    first = cycles[i].pop(0)
                    cycles[i].append(first)

        hits = [i for i in range(len(cycles)) if cycles[i] and cycles[i][0] == markers[i]]
        eliminated = len(hits) > 0

        if not eliminated and len(states) >= 1:
            marker = choose_unique_marker(markers, avoid=sym_n)
            L_new = (len(states) + 1) * S
            new_cycle = [marker] + [sym_n] * (L_new - 1)
            cycles.append(new_cycle)
            markers.append(marker)

        fronts = [c[0] for c in cycles if c]
        coherent = (not eliminated) and (len(fronts) == len(set(fronts)))

        states.append((
            n, position.copy(), [c.copy() for c in cycles], markers.copy(),
            hits.copy(), coherent, S, sym_n
        ))

    return states

def show_terminal(states):
    prev_cycle_count = 0

    for (n, position, cycles, markers, hits, coherent, S, sym_n) in states:
        t_prime = time_map(n)
        print(f"\n--- Krok {t_prime} | batch = {sym_n} ---")

        current_count = len(cycles)

        if current_count > prev_cycle_count:
            new_cycle = cycles[-1]
            idx = current_count
            count = len(new_cycle)
            if count > 5:
                display = ''.join(new_cycle[:5]) + f" ({count})"
            else:
                display = ''.join(new_cycle) + f" ({count})"
            print("Cykle:")
            print(f"  cykl {idx:>2}: {display}")
        else:
            pass

        if hits:
            print("⚡ UDERZENIA cykli")
        elif coherent:
            print("🌐 Pełna synchronizacja: brak uderzeń.")
        else:
            print("✅ Globalna zgoda: brak uderzeń, nowy cykl.")
        prev_cycle_count = current_count
    
    print("\n=== PODSUMOWANIE KOŃCOWE ===")
    if not states:
        print("Brak wygenerowanych stanów.")
        return
    last_state = states[-1]
    cycles = last_state[2]

    print("Cykle:")
    for idx, cycle in enumerate(cycles, start=1):
        count = len(cycle)
        if count > 5:
            display = ''.join(cycle[:5]) + f" ({count})"
        else:
            display = ''.join(cycle) + f" ({count})"
        print(f"  cykl {idx:>2}: {display}")

def time_map(n: int) -> int:
    return int(5 * (n ** 0.5)) + n  

def run():
    t0 = time.perf_counter()
    try:
        max_n = int(input("Podaj liczbę. (np. 20): ").strip())
    except ValueError:
        print("Nieprawidłowa liczba. Kończę.")
        return
    if max_n < 2:
        print("Minimum to 2. Kończę.")
        return
    if max_n > 1000:
        print("Maksimum to 1000. Kończę.")
        return

    elapsed_ms = int((time.perf_counter() - t0) * 1000)
    S = step_from_latency_ms(elapsed_ms % 10)

    states = prepare_states(max_n, S)
    show_terminal(states)

if __name__ == "__main__":
    run()
