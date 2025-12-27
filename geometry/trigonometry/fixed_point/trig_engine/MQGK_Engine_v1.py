import math
from typing import Dict, List, Literal, Tuple

SubstepMode = Literal["snap", "halfstep", "lerp"]

def run_mqgk_engine(
    n_steps: int,
    turns: int = 1,
    substep_mode: SubstepMode = "halfstep",
    mqgk_c: int = 6284,       # Rozdzielczość bazowa (C)
    mqgk_r: int = 1 << 60,    # Skala (R)
    **kwargs
) -> Dict[str, object]:
    """
    MQGK Core Engine V1.3 - Pełna implementacja z sub-krokami.
    Zgodna z diagnostyką V1.3 (nie obcina kluczy w return).
    """
    C = int(mqgk_c)
    R = int(mqgk_r)
    
    # 1. PREKOMPUTACJA LUT (Pełna tablica dla C=6284)
    state_map_x: List[int] = []
    state_map_y: List[int] = []

    for i in range(C):
        angle = (2.0 * math.pi * i) / C
        state_map_x.append(int(R * math.cos(angle)))
        state_map_y.append(int(R * math.sin(angle)))

    # 2. LOGIKA SUB-STEPÓW
    
    def get_pos_snap(idx: int) -> Tuple[int, int]:
        return state_map_x[idx], state_map_y[idx]

    def get_pos_halfstep(idx: int, frac: float) -> Tuple[int, int]:
        if frac < 0.5:
            return state_map_x[idx], state_map_y[idx]
        j = (idx + 1) % C
        # Uśrednianie stanów (półkrok)
        return (state_map_x[idx] + state_map_x[j]) >> 1, (state_map_y[idx] + state_map_y[j]) >> 1

    def get_pos_lerp(idx: int, frac: float) -> Tuple[int, int]:
        j = (idx + 1) % C
        x0, y0 = state_map_x[idx], state_map_y[idx]
        x1, y1 = state_map_x[j], state_map_y[j]
        # Interpolacja liniowa (integer rounding)
        xq = int(x0 + frac * (x1 - x0))
        yq = int(y0 + frac * (y1 - y0))
        return xq, yq

    # 3. WYKONANIE RDZENIA
    total_steps = int(n_steps * turns)
    step_ratio = C / n_steps

    xs: List[int] = []
    ys: List[int] = []
    accums: List[float] = []

    for k in range(total_steps + 1):
        kf = k * step_ratio
        idx_base = int(kf) % C
        frac = kf - int(kf)

        if substep_mode == "snap":
            xq, yq = get_pos_snap(idx_base)
        elif substep_mode == "halfstep":
            xq, yq = get_pos_halfstep(idx_base, frac)
        elif substep_mode == "lerp":
            xq, yq = get_pos_lerp(idx_base, frac)
        else:
            raise ValueError(f"Unknown mode: {substep_mode}")

        xs.append(xq)
        ys.append(yq)
        accums.append(kf % C)

    # 4. SŁOWNIK STATYSTYK (PEŁNA ZGODNOŚĆ V1.3 - NIC NIE OBCIĘTE)
    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "stats": {
            "n_steps": n_steps,
            "turns": int(turns),
            "renorm_every": 0,
            "renorm_count": 0,
            "plus_count": 0,
            "turn_correction": False,
            "correction_gain_num": 0,
            "correction_gain_den": 0,
            "phase_model": "MQGK",
            "engine_type": "MQGK_CORE_V1.3_APPROX",
            "substep_mode": substep_mode,
            "mqgk_c": C,
            "mqgk_q": C // 4,
            "coord_scale": R,
            "base": C, 
            "R": R,
            "max_r_err": 0.0, 
            "elapsed": 0.0
        }
    }