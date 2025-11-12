# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# diagnostics.py — raporty błędów i diagnostyka planera

import math
from .constants import FACTOR_SCALE, TWO_PI_FIXED

def report_planer_info(stats):
    print("\n=== DIAG: stałe i planer ===")
    print(f"n_steps:          {stats['n_steps']}")
    print(f"base:             {stats['base']}")
    print(f"R (reszta):       {stats['R']}")
    print(f"plus_count:       {stats['plus_count']}")
    print(f"renorm_count:     {stats['renorm_count']}")
    print(f"max |r-1|:        {stats['max_r_err']:.12e}")
    print(f"czas całkowity:   {stats['elapsed']:.6f} s")

def report_errors(xs_fixed, ys_fixed, accums_fixed):
    n = len(xs_fixed) - 1
    maxA = maxB = 0.0
    rmsA = rmsB = 0.0
    for i in range(len(xs_fixed)):
        x = xs_fixed[i] / FACTOR_SCALE
        y = ys_fixed[i] / FACTOR_SCALE
        thA = (2 * math.pi * i) / n
        dA = math.hypot(x - math.cos(thA), y - math.sin(thA))
        thB = accums_fixed[i] / FACTOR_SCALE
        dB = math.hypot(x - math.cos(thB), y - math.sin(thB))
        maxA = max(maxA, dA); rmsA += dA * dA
        maxB = max(maxB, dB); rmsB += dB * dB
    rmsA = math.sqrt(rmsA / len(xs_fixed))
    rmsB = math.sqrt(rmsB / len(xs_fixed))

    print("\n=== RAPORT BŁĘDÓW ===")
    print(f"A) ref=2π·i/n  | max={maxA:.3e}, RMS={rmsA:.3e}")
    print(f"B) ref=accum   | max={maxB:.3e}, RMS={rmsB:.3e}")
