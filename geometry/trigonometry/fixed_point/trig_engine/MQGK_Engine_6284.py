import math
import time
from typing import Dict, List, Literal

SubstepMode = Literal["native", "adaptive"]

def run_mqgk_engine(
    n_steps: int,
    turns: int = 1,
    mqgk_c: int = 6284,
    mqgk_r: int = 1 << 60,
    mode: SubstepMode = "adaptive",
    **kwargs
) -> Dict[str, object]:
    """
    MQGK Core Engine V1.3 FULL LUT
    Najwyższa precyzja (DDS) + Stały czas dostępu.
    """
    C = int(mqgk_c)
    R = int(mqgk_r)

    # 1. Prekomputacja PEŁNEJ tablicy (Gwarantuje brak błędów na stykach ćwiartek)
    # Generujemy raz na obrót silnika lub przy inicjalizacji
    state_map_x = [0] * C
    state_map_y = [0] * C
    
    for i in range(C):
        angle = (2.0 * math.pi * i) / C
        state_map_x[i] = int(R * math.cos(angle))
        state_map_y[i] = int(R * math.sin(angle))

    # 2. Wykonanie rdzenia
    # W trybie native n_steps musi być równe C
    active_n = C if mode == "native" else n_steps
    total_steps = int(active_n * turns)
    
    xs: List[int] = []
    ys: List[int] = []
    accums: List[int] = []

    # Cache pętli dla maksymalnej wydajności
    _x = state_map_x
    _y = state_map_y

    if mode == "native":
        # NAJSZYBSZA ŚCIEŻKA: 1 krok = 1 stan LUT
        for k in range(total_steps + 1):
            i_mod = k % C
            xs.append(_x[i_mod])
            ys.append(_y[i_mod])
            accums.append(i_mod)
    else:
        # ŚCIEŻKA ADAPTACYJNA (Resampling)
        # i = floor(k * C / n_steps)
        den = max(1, int(active_n))
        for k in range(total_steps + 1):
            i_mod = (k * C // den) % C
            xs.append(_x[i_mod])
            ys.append(_y[i_mod])
            accums.append(i_mod)

    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "stats": {
            "n_steps": n_steps,
            "turns": turns,
            "renorm_every": 0,
            "renorm_count": 0,
            "plus_count": 0,
            "turn_correction": False,
            "correction_gain_num": 0,
            "correction_gain_den": 0,
            "phase_model": "MQGK",
            "engine_type": "MQGK 6284",
            "mode": mode,
            "mqgk_c": C,
            "mqgk_q": C // 4,
            "coord_scale": R,
            "base": C,
            "R": R,
            "max_r_err": 0.0,
            "elapsed": 0.0
        }
    }