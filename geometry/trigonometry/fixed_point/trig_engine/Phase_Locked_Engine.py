# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# engine.py — relational trigonometry engine (Q1.60)
# PRODUCTION / BLACK-BOX VERSION

import math
import time
from .constants import *

# ============================================================
# FIXED-POINT UTILITIES
# ============================================================

def isqrt(n: int) -> int:
    if n <= 0:
        return 0
    x = 1 << ((n.bit_length() + 1) >> 1)
    while True:
        y = (x + n // x) >> 1
        if y >= x:
            return x
        x = y


def round_q(v128: int) -> int:
    return (v128 + (1 << (FRAC_BITS - 1))) >> FRAC_BITS


def unround_q(val_q: int) -> int:
    return val_q << FRAC_BITS


# ============================================================
# SMALL-ANGLE APPROXIMATION (Taylor 5)
# ============================================================

def small_angle_sin_cos_fixed(a_q: int):
    a2 = (a_q * a_q) >> FRAC_BITS
    a3 = (a2 * a_q) >> FRAC_BITS
    a4 = (a2 * a2) >> FRAC_BITS
    a5 = (a4 * a_q) >> FRAC_BITS
    s = a_q - (a3 // 6) + (a5 // 120)
    c = FACTOR_SCALE - (a2 >> 1) + (a4 // 24)
    return s, c


def orthonormalize_step(s_q: int, c_q: int):
    n = isqrt(s_q * s_q + c_q * c_q)
    if n == 0:
        return 0, FACTOR_SCALE
    s_q = (s_q * FACTOR_SCALE + n // 2) // n
    c_q = (c_q * FACTOR_SCALE + n // 2) // n
    return s_q, c_q


# ============================================================
# PHASE PLANNER (Bresenham / DDA)
# ============================================================

def phase_planner(n_steps: int):
    base = TWO_PI_FIXED // n_steps
    R = TWO_PI_FIXED - base * n_steps
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
# ROTATION CORE
# ============================================================

def rot_with_feedback(x_q: int, y_q: int, s_q: int, c_q: int, rx: int, ry: int):
    t = (x_q * c_q) - (y_q * s_q) + rx
    xr = round_q(t)
    rx = t - unround_q(xr)

    t = (x_q * s_q) + (y_q * c_q) + ry
    yr = round_q(t)
    ry = t - unround_q(yr)

    return xr, yr, rx, ry


def adaptive_normalize(x_q: int, y_q: int, r2_thresh_q120: int):
    target = FACTOR_SCALE * FACTOR_SCALE
    r2 = x_q * x_q + y_q * y_q
    if abs(r2 - target) > r2_thresh_q120:
        r = isqrt(r2)
        x_q = (x_q * FACTOR_SCALE + r // 2) // r
        y_q = (y_q * FACTOR_SCALE + r // 2) // r
        return x_q, y_q, True
    return x_q, y_q, False


# ============================================================
# PER-TURN CORRECTION PLANNER
# ============================================================

def correction_planner(steps_per_turn: int, corr_total: int):
    base = corr_total // steps_per_turn
    R = corr_total - base * steps_per_turn

    sign = 1 if R >= 0 else -1
    Rabs = abs(R)

    err = 0
    corr = []
    for _ in range(steps_per_turn):
        err += Rabs
        plus = 1 if err >= steps_per_turn else 0
        if plus:
            err -= steps_per_turn
        corr.append(base + plus * sign)

    return corr


# ============================================================
# MAIN ENGINE (BLACK BOX)
# ============================================================

def run_small_angle_engine(
    n_steps: int,
    turns: int = 1,
    renorm_every: int = 0,
    enable_turn_correction: bool = False,
    correction_gain_num: int = 1,
    correction_gain_den: int = 1,
):
    # --- renormalization threshold (same as research version)
    renorm_threshold_bits = 40
    base_thresh = 1 << (2 * FRAC_BITS - renorm_threshold_bits)
    scale_shift = max(0, (n_steps.bit_length() - 1) - 10)
    r2_thresh_q120 = max(1, base_thresh >> scale_shift)

    deltas, base, R, plus_count = phase_planner(n_steps)

    base_p1 = base + 1
    S0, C0 = orthonormalize_step(*small_angle_sin_cos_fixed(base))
    S1, C1 = orthonormalize_step(*small_angle_sin_cos_fixed(base_p1))

    x = FACTOR_SCALE
    y = 0
    rx = ry = 0

    xs = [x]
    ys = [y]
    boundary_errs = []
    accums = [0]

    corr_deltas = [0] * n_steps
    total_steps = n_steps * max(1, int(turns))
    accum = 0
    renorm_count = 0

    for k in range(1, total_steps + 1):
        idx = (k - 1) % n_steps
        dlt = deltas[idx] + (corr_deltas[idx] if enable_turn_correction else 0)

        if dlt == base:
            s, c = S0, C0
        elif dlt == base_p1:
            s, c = S1, C1
        else:
            s, c = orthonormalize_step(*small_angle_sin_cos_fixed(dlt))

        x, y, rx, ry = rot_with_feedback(x, y, s, c, rx, ry)

        if renorm_every and (k % renorm_every == 0):
            x, y = orthonormalize_step(x, y)
            rx = ry = 0
            renorm_count += 1
        else:
            x, y, did = adaptive_normalize(x, y, r2_thresh_q120)
            if did:
                renorm_count += 1

        xs.append(x)
        ys.append(y)
        accum += dlt
        accums.append(accum)

        if enable_turn_correction and (k % n_steps == 0):
            err_q = (y * correction_gain_num) // correction_gain_den
            boundary_errs.append(abs(err_q))
            corr_deltas = correction_planner(n_steps, -err_q)

    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "stats": {
            "n_steps": n_steps,
            "turns": int(turns),
            "renorm_every": renorm_every,
            "renorm_count": renorm_count,
            "turn_correction": enable_turn_correction,
            "correction_gain_num": correction_gain_num,
            "correction_gain_den": correction_gain_den,
            "plus_count": plus_count,
            "base": base,
            "R": R,
            "coord_scale": FACTOR_SCALE,          # Q1.60
            "phase_model": "CONTINUOUS_LOCKED",   # faza ciągła + korekcja
            "engine_type": "PHASE_LOCKED_ENGINE",
        },
    }
