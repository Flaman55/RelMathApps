# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# benchmark.py — engine-agnostic benchmark (FINAL with Correct Resolution)

import math
import time

from .constants import FACTOR_SCALE
from .diagnostics import compute_drift_metrics


# ============================================================
# BENCHMARK — PERFORMANCE + GEOMETRIC ACCURACY
# ============================================================
def reference_point(i, n, t, phase_model):
    """
    Zwraca punkt referencyjny (x_ref, y_ref) dla danego modelu fazy.
    """
    if phase_model == "MQGK":
        th = (2.0 * math.pi * i) / n
        return math.cos(th), math.sin(th)
    else:
        return math.cos(t), math.sin(t)


def benchmark(
    engine_cfg,
    steps_list=(128, 256, 512, 1024, 2048),
    turns_bench=100,
    stats=None,
):
    engine = engine_cfg["engine"]
    name   = engine_cfg["name"]

    renorm_every = engine_cfg.get("renorm_every", 0)
    enable_turn_correction = engine_cfg.get("enable_turn_correction", False)
    correction_gain_num = engine_cfg.get("correction_gain_num", 1)
    correction_gain_den = engine_cfg.get("correction_gain_den", 1)

    print(f"\n=== BENCHMARK ({name}, {turns_bench} TURNS) ===")
    rows = []

    for n in steps_list:
        # ----------------------------------------------------
        # ENGINE RUN (TIME MEASURED ONLY HERE)
        # ----------------------------------------------------
        t0 = time.perf_counter()

        result = engine(
            n_steps=n,
            turns=turns_bench,
            renorm_every=renorm_every,
            enable_turn_correction=enable_turn_correction,
            correction_gain_num=correction_gain_num,
            correction_gain_den=correction_gain_den,
        )

        elapsed = time.perf_counter() - t0
        time_per_turn = elapsed / max(1, turns_bench)


        stats = result["stats"]
        phase_model = stats.get("phase_model", "CONTINUOUS")

        xs = result["xs"]
        ys = result["ys"]
        acc = result["accums"]

        # ----------------------------------------------------
        # FAKTYCZNA ROZDZIELCZOŚĆ KĄTOWA (POPRAWKA KLUCZOWA)
        # ----------------------------------------------------
        if phase_model == "MQGK":
            effective_n = int(stats.get("mqgk_c", n))
        else:
            effective_n = int(n)

        effective_n = max(1, effective_n)

        deg_per_step = 360.0 / effective_n
        mm_arc_per_step = 1000.0 * (2.0 * math.pi / effective_n)

        # ----------------------------------------------------
        # GEOMETRIC ERROR — ARCHITECTURE-SPECIFIC
        # ----------------------------------------------------
        max_err = 0.0
        rms_acc = 0.0
        
        # 1. Pobieramy właściwą skalę z silnika
        scale = stats.get("coord_scale", FACTOR_SCALE)
        if scale == 0: scale = FACTOR_SCALE

        # 2. Rozróżniamy metody pomiaru
        is_mqgk = (phase_model == "MQGK")

        # Ustalamy ile punktów sprawdzić (zawsze jeden pełny obrót)
        n_to_check = effective_n if is_mqgk else n

        for i in range(n_to_check + 1):
            if i >= len(xs): break
            
            x_norm = xs[i] / scale
            y_norm = ys[i] / scale
            
            if is_mqgk:
                # DLA BQGK: Referencja to IDEALNY stan LUT o indeksie i_mod
                # (zakładamy, że silnik podaje punkty po kolei wzdłuż LUT)
                current_idx = acc[i] if (acc and i < len(acc)) else i
                th_ref = (2.0 * math.pi * (current_idx % effective_n)) / effective_n
            else:
                # DLA PLE/CORDIC: Referencja to podział okręgu na 'n' części
                th_ref = (2.0 * math.pi * i) / n
            
            x_ref = math.cos(th_ref)
            y_ref = math.sin(th_ref)

            d = math.hypot(x_norm - x_ref, y_norm - y_ref)

            if d > max_err:
                max_err = d
            rms_acc += d * d

        rms_err = math.sqrt(rms_acc / (n_to_check + 1))

        if phase_model == "MQGK":
            engine_steps_per_turn = int(stats.get("mqgk_c", n))
            total_steps = engine_steps_per_turn * turns_bench
        else:
            total_steps = n * turns_bench

        time_per_step_ns = (elapsed / max(1, total_steps)) * 1e9
        # Przeliczenie całkowitego czasu na milisekundy
        elapsed_ms = elapsed * 1000.0
        time_per_turn_ms = (elapsed / max(1, turns_bench)) * 1000.0


        print(
            f"n={n:5d} | "
            f"res_base={effective_n:5d} | "
            f"deg/step={deg_per_step:8.4f}° | "
            f"max_err={max_err:.3e} | "
            f"time total={elapsed_ms:8.3f}ms | "
            f"time/turn={time_per_turn_ms:8.3f} ms"
        )

        rows.append((n, max_err, rms_err, time_per_step_ns, deg_per_step, mm_arc_per_step))

    return rows


# ============================================================
# LONG-TERM DRIFT TEST
# ============================================================

def drift_test(
    engine_cfg,
    steps_per_turn=1024,
    turns=3000,
    metric="radius",
):
    engine = engine_cfg["engine"]
    name   = engine_cfg["name"]

    renorm_every = engine_cfg.get("renorm_every", 0)
    enable_turn_correction = engine_cfg.get("enable_turn_correction", False)
    correction_gain_num = engine_cfg.get("correction_gain_num", 1)
    correction_gain_den = engine_cfg.get("correction_gain_den", 1)

    print(f"\n=== DRIFT TEST ({name}) ===")

    t0 = time.perf_counter()

    result = engine(
        n_steps=steps_per_turn,
        turns=turns,
        renorm_every=renorm_every,
        enable_turn_correction=enable_turn_correction,
        correction_gain_num=correction_gain_num,
        correction_gain_den=correction_gain_den,
    )

    elapsed = time.perf_counter() - t0

    stats = result["stats"]
    total_steps = stats["n_steps"] * stats["turns"]

    drift_stats = compute_drift_metrics(
        result["xs"], result["ys"], stats, metric
    )

    err_start = drift_stats["start"]
    err_end   = drift_stats["end"]
    err_max   = drift_stats["max"]
    err_min   = drift_stats["min"]
    avg_step  = drift_stats["avg_step"]
    drift_turn = avg_step * steps_per_turn
    time_per_step_ns = (elapsed / total_steps) * 1e9

    if "max_r_err_q120" in stats:
        max_r_err = stats["max_r_err_q120"] / (FACTOR_SCALE * FACTOR_SCALE)
    else:
        max_r_err = stats.get("max_r_err", 0.0)

    print(f"steps/turn:              {steps_per_turn}")
    print(f"turns:                   {turns}")
    print(f"total steps:             {total_steps}")
    print(f"renorm_every:            {renorm_every}")
    print(f"renorm_count:            {stats['renorm_count']}")
    print(
        f"turn_correction:         {enable_turn_correction}  "
        f"gain={correction_gain_num}/{correction_gain_den}"
    )
    print(f"metric:                  {metric}")
    print(f"start error:             {err_start:.3e}")
    print(f"end error:               {err_end:.3e}")
    print(f"max error:               {err_max:.3e}")
    print(f"min error:               {err_min:.3e}")
    print(f"avg delta/step:          {avg_step:.3e}")
    print(f"drift per turn:          {drift_turn:.3e}")
    print(f"time total:              {elapsed:.6f} s")
    print(f"time/step:               {time_per_step_ns:.1f} ns")
    print(f"max |r²−1|:              {max_r_err:.3e}")

    return {
        "metrics": drift_stats,
        "elapsed": elapsed,
        "renorm_count": stats["renorm_count"],
    }


# ============================================================
# COMPARISON TABLE
# ============================================================

def print_comparison_table(results):
    print("\n=== ENGINE COMPARISON SUMMARY ===\n")

    header = (
        f"{'Engine':24s} | {'n':>6s} | {'deg/step':>10s} | {'mm@1m':>10s} | "
        f"{'max_err':>11s} | {'time/step [ns]':>14s}"
    )
    print(header)
    print("-" * len(header))

    for engine_name, rows in results.items():
        for (n, max_err, rms_err, t_ns, deg_s, mm_s) in rows:
            print(
                f"{engine_name:24s} | "
                f"{n:6d} | "
                f"{deg_s:9.4f}° | "
                f"{mm_s:8.3f}mm | "
                f"{max_err:11.3e} | "
                f"{t_ns:14.1f}"
            )
        print("-" * len(header))
