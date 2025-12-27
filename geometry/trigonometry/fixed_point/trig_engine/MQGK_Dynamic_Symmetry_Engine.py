import math
import time
from typing import Dict, List, Tuple

def get_prime_for_precision(symmetry: int, precision_decimal: int) -> Tuple[int, int]:
    """
    Znajduje liczbę pierwszą P, aby (symmetry * P) najdokładniej 
    odwzorowało 2*Pi * 10^precision.
    """
    # Lista rozszerzalna - silnik sam dobierze najlepszą
    primes_pool = [157, 311, 1229, 1571, 3943, 7879, 19709, 39419, 78853, 157259]
    target_2pi = int(2 * math.pi * (10 ** precision_decimal))
    
    best_p = primes_pool[0]
    min_diff = float('inf')
    
    for p in primes_pool:
        c_candidate = symmetry * p
        diff = abs(c_candidate - target_2pi)
        if diff < min_diff:
            min_diff = diff
            best_p = p
            
    return best_p, symmetry * best_p

def run_mqgk_prototype(
    symmetry: int,       # Podział: 4, 16, 64, 512...
    precision: int,      # Wykładnik 10^n dla 2Pi
    turns: int = 1,
    mqgk_r: int = 1 << 60,
    mode: str = "native",
    n_steps: int = 0     # Tylko dla trybu adaptive
) -> Dict:
    
    t_start = time.perf_counter()
    
    # 1. Dobór parametrów na podstawie Twojej logiki
    p_val, C = get_prime_for_precision(symmetry, precision)
    R = mqgk_r
    
    # 2. Budowa tabeli LUT (Wersja bazowa dla prototypu)
    # Tutaj w przyszłości wejdzie Twój mechanizm 'tan' do optymalizacji sektorów
    lut_x = [0] * C
    lut_y = [0] * C
    
    for i in range(C):
        angle = (2.0 * math.pi * i) / C
        lut_x[i] = int(R * math.cos(angle))
        lut_y[i] = int(R * math.sin(angle))

    # 3. Wybór rozdzielczości procesowej
    active_steps = C if mode == "native" else n_steps
    total_iterations = int(active_steps * turns)
    
    xs, ys, accums = [], [], []
    
    # 4. Rdzeń wykonawczy (Fixed-Point Phase Accumulator)
    for k in range(total_iterations + 1):
        # Index phase (modulo C zapewnia cykliczność)
        i_mod = (k * C // active_steps) % C
        
        xs.append(lut_x[i_mod])
        ys.append(lut_y[i_mod])
        accums.append(i_mod)

    t_end = time.perf_counter()

    return {
        "xs": xs,
        "ys": ys,
        "stats": {
            "symmetry_base": symmetry,
            "selected_prime": p_val,
            "engine_base_C": C,
            "target_2pi": int(2 * math.pi * (10 ** precision)),
            "precision_error": C - int(2 * math.pi * (10 ** precision)),
            "elapsed_ms": (t_end - t_start) * 1000
        }
    }

def verify_mqgk_metric(r_mm: int = 1000, test_turns: int = 100):
    # Inicjalizacja silnika (C = 629248)
    C = 629248
    result = run_mqgk_prototype(n_steps=C, turns=test_turns, mqgk_c=C, r_mm=r_mm, mode="native")
    
    stats = result["stats"]
    total_steps = len(result["distances_nm"]) - 1
    last_dist_nm = result["distances_nm"][-1]
    
    # Obliczamy oczekiwany dystans teoretyczny: turns * ideal_circ
    ideal_circ = stats["metric_ideal_circ_nm"]
    expected_total_nm = test_turns * ideal_circ
    
    # Obliczamy dryf
    drift_nm = last_dist_nm - expected_total_nm
    
    print(f"=== MQGK METRIC VERIFIER (C={C}) ===")
    print(f"Liczba obrotów      : {test_turns}")
    print(f"Całkowita l. kroków : {total_steps}")
    print(f"Wzorzec obwodu (nm) : {ideal_circ}")
    print(f"Oczekiwany dystans  : {expected_total_nm} nm")
    print(f"Uzyskany dystans    : {last_dist_nm} nm")
    print(f"DRYF METRYCZNY      : {drift_nm} nm")
    print("-" * 40)
    
    if drift_nm == 0:
        print("STATUS: PERFEKCYJNA ZGODNOŚĆ (ZERO DRIFT)")
    else:
        print(f"STATUS: WYKRYTO RÓŻNICĘ {drift_nm} nm")

# --- TEST PROTOTYPU ---
# Przykład: Symetria 512, precyzja 6 (celujemy w 6 283 185)
res = run_mqgk_prototype(symmetry=512, precision=3, mode="native")
# verify_mqgk_metric(test_turns=10)

stats = res["stats"]
print(f"Baza silnika (C): {stats['engine_base_C']}")
print(f"Wybrana liczba pierwsza: {stats['selected_prime']}")
print(f"Błąd odwzorowania 2Pi: {stats['precision_error']} jednostek")
print(f"Czas generowania: {stats['elapsed_ms']:.2f} ms")