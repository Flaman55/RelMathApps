# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# engine.py — silnik relacyjnej trygonometrii (Q1.60)

import math, time
from .constants import *

def isqrt(n: int) -> int:
    if n <= 0: return 0
    x = 1 << ((n.bit_length() + 1) >> 1)
    while True:
        y = (x + n // x) >> 1
        if y >= x: return x
        x = y

def round_q(v128: int) -> int:
    return (v128 + (1 << (FRAC_BITS - 1))) >> FRAC_BITS

def unround_q(val_q: int) -> int:
    return val_q << FRAC_BITS

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
    if n == 0: return 0, FACTOR_SCALE
    s_q = (s_q * FACTOR_SCALE + n // 2) // n
    c_q = (c_q * FACTOR_SCALE + n // 2) // n
    return s_q, c_q

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

def rot_with_feedback(x_q: int, y_q: int, s_q: int, c_q: int, rx: int, ry: int):
    t = (x_q * c_q) - (y_q * s_q) + rx
    xr = round_q(t); rx = t - unround_q(xr)
    t = (x_q * s_q) + (y_q * c_q) + ry
    yr = round_q(t); ry = t - unround_q(yr)
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

def run_small_angle_engine(n_steps=1000, renorm_threshold_bits=40, precompute=True):
    r2_thresh_q120 = 1 << (2 * FRAC_BITS - renorm_threshold_bits)
    x = FACTOR_SCALE
    y = 0
    rx = ry = 0
    xs, ys, accums = [x], [y], [0]

    deltas, base, R, plus_count = phase_planner(n_steps)

    if precompute:
        base_p1 = base + 1
        S0, C0 = small_angle_sin_cos_fixed(base); S0, C0 = orthonormalize_step(S0, C0)
        S1, C1 = small_angle_sin_cos_fixed(base_p1); S1, C1 = orthonormalize_step(S1, C1)

    accum = 0
    renorm_count = 0
    max_r_err = 0.0
    t0 = time.perf_counter()

    for dlt in deltas:
        if precompute:
            s, c = (S0, C0) if dlt == base else (S1, C1)
        else:
            s, c = small_angle_sin_cos_fixed(dlt)
            s, c = orthonormalize_step(s, c)
        x, y, rx, ry = rot_with_feedback(x, y, s, c, rx, ry)
        x, y, did = adaptive_normalize(x, y, r2_thresh_q120)
        if did:
            renorm_count += 1

        r = math.hypot(x / FACTOR_SCALE, y / FACTOR_SCALE)
        max_r_err = max(max_r_err, abs(r - 1.0))

        xs.append(x)
        ys.append(y)
        accum += dlt
        accums.append(accum)
    elapsed = time.perf_counter() - t0

    return {
        "xs": xs,
        "ys": ys,
        "accums": accums,
        "stats": {
            "n_steps": n_steps,
            "renorm_count": renorm_count,
            "max_r_err": max_r_err,
            "elapsed": elapsed,
            "plus_count": plus_count,
            "base": base,
            "R": R
        }
    }
