# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# engine_cordic_incremental.py — commercial-style CORDIC oscillator (Q1.60)

import math
from .constants import FRAC_BITS, FACTOR_SCALE, TWO_PI_FIXED

# ============================================================
# PHASE PLANNER (IDENTYCZNY)
# ============================================================

def phase_planner(n_steps: int):
    base = TWO_PI_FIXED // n_steps
    R    = TWO_PI_FIXED - base * n_steps
    err = 0
    deltas = []
    plus_count = 0
    for _ in range(n_steps):
        err += R
        plus = 1 if err >= n_steps else 0
        if plus:
            err -= n_steps
            plus_count += 1
        deltas.append(base + plus)
    return deltas, base, R, plus_count

# ============================================================
# CORDIC TABLE (ROTATION MODE)
# ============================================================

N_ITER = 60

ATAN_TABLE = [
    int(round(math.atan(2.0 ** -i) * FACTOR_SCALE))
    for i in range(N_ITER)
]

# K = Π 1/sqrt(1 + 2^(-2i))  (so gain G ≈ 1/K)
_K = 1.0
for i in range(N_ITER):
    _K *= 1.0 / math.sqrt(1.0 + 2.0 ** (-2 * i))
K_Q60 = int(round(_K * FACTOR_SCALE))

def mul_q60(a_q60: int, b_q60: int) -> int:
    # (a*b) in Q2.120 -> back to Q1.60
    return (a_q60 * b_q60) >> FRAC_BITS

# ============================================================
# CORDIC ROTATION CORE
# ============================================================

def cordic_rotate_incremental(x_q: int, y_q: int, theta_q: int):
    """
    Rotation-mode CORDIC by theta_q (Q1.60). Returns (x,y) with gain G applied.
    """
    z = theta_q
    for i in range(N_ITER):
        dx = y_q >> i
        dy = x_q >> i
        if z >= 0:
            x_q -= dx
            y_q += dy
            z   -= ATAN_TABLE[i]
        else:
            x_q += dx
            y_q -= dy
            z   += ATAN_TABLE[i]
    return x_q, y_q

# ============================================================
# ENGINE — CORDIC OSCILLATOR (COMMERCIAL STYLE: GAIN-COMPENSATED)
# ============================================================

def run_small_angle_engine(
    n_steps=1000,
    renorm_threshold_bits=40,      # ignored (API compatibility)
    precompute=True,               # ignored
    turns=1,
    enable_turn_correction=False,  # ignored (API compatibility)
    correction_gain_num=1,         # ignored
    correction_gain_den=1,         # ignored
    renorm_every=0,                # ignored (CORDIC keeps amplitude via K)
):
    # Start from true unit vector in Q1.60
    x = FACTOR_SCALE
    y = 0

    xs = [x]
    ys = [y]
    accums = [0]

    deltas, base, R, plus_count = phase_planner(n_steps)

    total_steps = n_steps * max(1, int(turns))
    accum = 0

    # radius error tracking as Q2.120 (no floats)
    target_q120 = FACTOR_SCALE * FACTOR_SCALE
    max_r_err_q120 = 0

    renorm_count = 0  # not used here (amplitude controlled by K each step)

    for k in range(1, total_steps + 1):
        idx = (k - 1) % n_steps
        dlt = deltas[idx]

        # rotate by small delta (gain G applied internally)
        x, y = cordic_rotate_incremental(x, y, dlt)

        # compensate gain per step (commercial scaled oscillator)
        x = mul_q60(x, K_Q60)
        y = mul_q60(y, K_Q60)

        # --- DODANA KOREKCJA BŁĘDU (TURN CORRECTION) ---
        if enable_turn_correction and (k % n_steps == 0):
            x = FACTOR_SCALE
            y = 0
            renorm_count += 1
        # -----------------------------------------------

        # fixed-point norm error (r^2 in Q2.120)
        r2 = x * x + y * y
        err_q120 = r2 - target_q120
        if err_q120 < 0:
            err_q120 = -err_q120
        if err_q120 > max_r_err_q120:
            max_r_err_q120 = err_q120

        accum += dlt
        xs.append(x)
        ys.append(y)
        accums.append(accum)

    # W słowniku stats zmieńmy też flagę na enable_turn_correction
    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "stats": {
            "n_steps": int(n_steps),
            "turns": int(turns),
            "renorm_every": 0,
            "renorm_count": renorm_count,
            "turn_correction": enable_turn_correction, # teraz odzwierciedla stan
            "correction_gain_num": 0,
            "correction_gain_den": 0,
            "plus_count": plus_count,
            "base": base,
            "R": R,
            "max_r_err_q120": max_r_err_q120,
            "coord_scale": FACTOR_SCALE,          # Q1.60
            "phase_model": "CONTINUOUS_INCREMENTAL",
            "engine_type": "CORDIC_INCREMENTAL",
        },
    }
