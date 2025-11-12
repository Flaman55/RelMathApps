# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# benchmark.py — testy wydajności i dokładności

import math
from .engine import run_small_angle_engine
from .constants import FACTOR_SCALE

def benchmark(steps_list=(128, 256, 512, 1024, 2048)):
    print("\n=== BENCHMARK ===")
    rows = []
    for n in steps_list:
        result = run_small_angle_engine(n_steps=n, renorm_threshold_bits=40, precompute=True)
        xs, ys, acc = result["xs"], result["ys"], result["accums"]
        max_err, rms_acc = 0.0, 0.0
        for i in range(len(xs)):
            x, y, t = xs[i] / FACTOR_SCALE, ys[i] / FACTOR_SCALE, acc[i] / FACTOR_SCALE
            dx, dy = x - math.cos(t), y - math.sin(t)
            d = math.hypot(dx, dy)
            max_err = max(max_err, d); rms_acc += d * d
        rms_err = math.sqrt(rms_acc / len(xs))
        t_per_step_ns = (result["stats"]["elapsed"] / n) * 1e9
        print(f"n={n:5d} | max_err={max_err:.3e}, rms={rms_err:.3e}, time/step={t_per_step_ns:8.1f} ns")
        rows.append((n, max_err, rms_err, t_per_step_ns))
    return rows
