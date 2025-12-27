import math
from typing import Dict, List, Literal

SubstepMode = Literal["native", "adaptive"]

def run_mqgk_engine(
    n_steps: int,
    turns: int = 1,
    mqgk_c: int = 628,       # Domyślna rozdzielczość dla V1
    mqgk_r: int = 1 << 60,   # Ta sama skala co w 6284
    mode: SubstepMode = "native",
    **kwargs,                # Ignoruje dodatkowe parametry PLE
) -> Dict[str, object]:
    """
    MQGK Core Engine V1.0 (BQGK 628)
    Zaktualizowany do pełnej zgodności z diagnostyką V1.3.
    """

    C = int(mqgk_c)
    R = int(mqgk_r)

    if n_steps != C:
        n_steps = C
    
    # W trybie native narzucamy architektoniczne C
    if mode == "native":
        n_steps = C

    # 1. Prekomputacja (BQGK V1 używa pełnej tablicy, nie ćwiartki)
    state_map_x: List[int] = []
    state_map_y: List[int] = []

    for i in range(C):
        angle = (2.0 * math.pi * i) / C
        state_map_x.append(int(R * math.cos(angle)))
        state_map_y.append(int(R * math.sin(angle)))

    # 2. Wykonanie rdzenia
    total_steps = int(n_steps) * int(turns)
    
    xs: List[int] = []
    ys: List[int] = []
    accums: List[int] = []

    if mode == "native":
        for k in range(total_steps + 1):
            i_mod = k % C
            xs.append(state_map_x[i_mod])
            ys.append(state_map_y[i_mod])
            accums.append(i_mod)
    else:
        # Tryb adaptive (resampling)
        den = max(1, int(n_steps))
        for k in range(total_steps + 1):
            i_mod = (k * C // den) % C
            xs.append(state_map_x[i_mod])
            ys.append(state_map_y[i_mod])
            accums.append(i_mod)

    # 3. Słownik kompatybilności (Identyczny jak w wersji 6284)
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
            "engine_type": "MQGK V1",
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