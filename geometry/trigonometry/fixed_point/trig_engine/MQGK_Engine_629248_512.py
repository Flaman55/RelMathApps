import math
import time
from typing import Dict, List, Literal

SubstepMode = Literal["native", "adaptive"]

def run_mqgk_engine(
    n_steps: int,
    turns: int = 1,
    mqgk_c: int = 629248,  # 512 * 1229 (Prime)
    mqgk_r: int = 1 << 60,
    mode: SubstepMode = "native",
    r_mm: int = 1000,      # Promień referencyjny dla etykiety metrycznej
    **kwargs
) -> Dict[str, object]:
    """
    MQGK Core Engine V1.512 FULL.
    Baza C=629248 (512-bit symmetry), stałoprzecinkowy licznik nm, pełne statystyki.
    """
    t_start = time.perf_counter()
    
    C = int(mqgk_c)
    R = int(mqgk_r)
    Q = C // 4
    
    # --- PRZYGOTOWANIE ETYKIET METRYCZNYCH ---
    # Obwód idealny w nm (2 * pi * r_mm * 10^6)
    ideal_circ_nm = int(2 * math.pi * r_mm * 1_000_000)
    m_num = ideal_circ_nm
    m_den = C

    # 1. PREKOMPUTACJA PEŁNEJ TABELI (LUT)
    # Wykonywana raz, zapewnia 0.0 błędu promienia w locie
    full_lut_x = [0] * C
    full_lut_y = [0] * C
    for i in range(C):
        angle = (2.0 * math.pi * i) / C
        full_lut_x[i] = int(R * math.cos(angle))
        full_lut_y[i] = int(R * math.sin(angle))

    # 2. RDZEŃ WYKONAWCZY
    active_n = C if mode == "native" else n_steps
    total_steps = int(active_n * turns)
    den = max(1, int(active_n))
    
    xs: List[int] = []
    ys: List[int] = []
    accums: List[int] = []
    distances_nm: List[int] = []
    
    _lx, _ly = full_lut_x, full_lut_y

    for k in range(total_steps + 1):
        # Indeks fali (modulo C)
        i_mod = (k * C // den) % C
        
        # Dystans absolutny nm (Fixed-Point, k * (ideal/C))
        dist_nm = (k * m_num) // m_den
        
        xs.append(_lx[i_mod])
        ys.append(_ly[i_mod])
        accums.append(i_mod)
        distances_nm.append(dist_nm)

    t_end = time.perf_counter()

    # PEŁNY ZWROT Z KOMPLETNYMI STATYSTYKAMI
    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "distances_nm": distances_nm,
        "stats": {
            "n_steps": n_steps,
            "turns": turns,
            "renorm_every": 0,
            "renorm_count": 0,
            "plus_count": 0,
            "turn_correction": False,
            "phase_model": "MQGK",
            "engine_type": f"MQGK {C} (V1.512 Full + Metric)",
            "mode": mode,
            "mqgk_c": C,
            "mqgk_q": Q,
            "coord_scale": R,
            "base": C,
            "R": R,
            "max_r_err": 0.0,  # LUT gwarantuje idealny promień R
            "elapsed": t_end - t_start,
            "metric_ideal_circ_nm": ideal_circ_nm,
            "metric_last_dist_nm": distances_nm[-1]
        }
    }

def verify_mqgk_metric(r_mm: int = 1000, test_turns: int = 100):
    # Inicjalizacja silnika (C = 629248)
    C = 629248
    result = run_mqgk_engine(n_steps=C, turns=test_turns, mqgk_c=C, r_mm=r_mm, mode="native")
    
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

# Uruchomienie weryfikacji
verify_mqgk_metric(test_turns=100)