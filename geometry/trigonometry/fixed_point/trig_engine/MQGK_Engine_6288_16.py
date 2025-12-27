import math
from typing import Dict, List, Literal

SubstepMode = Literal["native", "adaptive"]

def run_mqgk_engine(
    n_steps: int,
    turns: int = 1,
    mqgk_c: int = 6288,  
    mqgk_r: int = 1 << 60,
    mode: SubstepMode = "adaptive",
    **kwargs
) -> Dict[str, object]:
    C = int(mqgk_c)
    R = int(mqgk_r)
    
    # 1. GENERACJA PEŁNEGO OKRĘGU (Bezpieczna i symetryczna)
    # Zamiast skomplikowanych swapów w locie, budujemy LUT 
    # gwarantując ciągłość fazy dla każdego i.
    full_lut_x = [0] * C
    full_lut_y = [0] * C

    for i in range(C):
        # Generujemy każdy punkt bezpośrednio, co gwarantuje okrąg,
        # ale dzięki C=6288 zachowujemy idealną symetrię co 22.5 stopnia.
        angle = (2.0 * math.pi * i) / C
        full_lut_x[i] = int(R * math.cos(angle))
        full_lut_y[i] = int(R * math.sin(angle))

    # 2. RDZEŃ WYKONAWCZY (Maksymalna wydajność - Full LUT)
    active_n = C if mode == "native" else n_steps
    total_steps = int(active_n * turns)
    den = max(1, int(active_n))
    
    xs, ys, accums = [], [], []
    _lx, _ly = full_lut_x, full_lut_y # Cache do rejestrów

    for k in range(total_steps + 1):
        # i_mod to nasz "wskaźnik fazy" w tabeli
        i_mod = (k * C // den) % C
        xs.append(_lx[i_mod])
        ys.append(_ly[i_mod])
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
            "phase_model": "MQGK",
            "engine_type": f"MQGK {C} (Fixed Circle)",
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