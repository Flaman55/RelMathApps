# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# diagnostics.py — raporty błędów i diagnostyka planera

import math
from .constants import FACTOR_SCALE, TWO_PI_FIXED

def get_coord_scale(stats):
    """
    Zwraca skalę współrzędnych dla danego silnika.
    """
    return stats.get("coord_scale", FACTOR_SCALE)

def report_planer_info(stats):
    print("\n=== DIAG: stałe i planer ===")
    print(f"n_steps:          {stats['n_steps']}")
    print(f"base:             {stats['base']}")
    print(f"R (reszta):       {stats['R']}")
    print(f"plus_count:       {stats['plus_count']}")
    print(f"renorm_count:     {stats['renorm_count']}")
    print(f"max |r-1|:        {stats['max_r_err']:.12e}")
    print(f"czas całkowity:   {stats['elapsed']:.6f} s")

def report_errors(xs_fixed, ys_fixed, accums_fixed, stats):
    if not isinstance(xs_fixed, (list, tuple)):
        raise TypeError(
            f"xs_fixed must be list/tuple, got {type(xs_fixed)}"
        )

    scale = get_coord_scale(stats)
    phase_model = stats.get("phase_model", "UNKNOWN")

    n = len(xs_fixed) - 1

    # --- DODANE: OBLICZENIA ROZDZIELCZOŚCI ---
    deg_per_step = 360.0 / n
    mm_per_step_1m = 1000.0 * (2.0 * math.pi / n)
    print(f"\n=== PARAMETRY GEOMETRYCZNE ===")
    print(f"Rozdzielczość kątowa : {deg_per_step:.6f}° na krok")
    print(f"Rozdzielczość łuku 1m: {mm_per_step_1m:.6f} mm")
    # -----------------------------------------

    # ------------------------------------------------------------
    # MODELE CIĄGŁE: Phase / CORDIC
    # ------------------------------------------------------------
    if phase_model != "MQGK":
        maxA = maxB = 0.0
        rmsA = rmsB = 0.0

        for i in range(len(xs_fixed)):
            x = xs_fixed[i] / scale
            y = ys_fixed[i] / scale

            thA = (2 * math.pi * i) / n
            dA = math.hypot(x - math.cos(thA), y - math.sin(thA))

            thB = accums_fixed[i] / scale
            dB = math.hypot(x - math.cos(thB), y - math.sin(thB))

            maxA = max(maxA, dA)
            rmsA += dA * dA
            maxB = max(maxB, dB)
            rmsB += dB * dB

        rmsA = math.sqrt(rmsA / len(xs_fixed))
        rmsB = math.sqrt(rmsB / len(xs_fixed))

        print("\n=== RAPORT BŁĘDÓW (MODEL CIĄGŁY) ===")
        print(f"A) ref=2π·i/n  | max={maxA:.3e}, RMS={rmsA:.3e}")
        print(f"B) ref=accum   | max={maxB:.3e}, RMS={rmsB:.3e}")

        return

    # ------------------------------------------------------------
    # MODEL STRUKTURALNY: MQGK
    # ------------------------------------------------------------
    x0 = xs_fixed[0] / scale
    y0 = ys_fixed[0] / scale
    xN = xs_fixed[-1] / scale
    yN = ys_fixed[-1] / scale

    closure_error = math.hypot(xN - x0, yN - y0)

    # stabilność promienia
    radii_err = [
        abs(math.hypot(x / scale, y / scale) - 1.0)
        for x, y in zip(xs_fixed, ys_fixed)
    ]

    max_r_err = max(radii_err)
    avg_r_err = sum(radii_err) / len(radii_err)

    print("\n=== RAPORT STRUKTURALNY (MQGK) ===")
    print(f"Domknięcie cyklu |ΔP| : {closure_error:.3e}")
    # DODANE: Przeliczenie błędu promienia na mikrony
    print(f"Max |r−1|         : {max_r_err:.3e} ({max_r_err*1000000:.3f} μm @ 1m)")
    print(f"Avg |r−1|         : {avg_r_err:.3e}")
    print(f"Stany cyklu       : {stats.get('base', '628-fixed')}")

def compute_drift_metrics(xs, ys, stats, metric="radius"):
    from math import hypot

    scale = stats.get("coord_scale", FACTOR_SCALE)
    
    # Jeśli scale jest typem (np. <class 'int'>), a nie liczbą
    if isinstance(scale, type):
        return FACTOR_SCALE

    errs = []
    x0, y0 = xs[0], ys[0]

    for xq, yq in zip(xs, ys):
        x = xq / scale
        y = yq / scale

        if metric == "radius":
            e = abs(hypot(x, y) - 1.0)
        elif metric == "dist_to_start":
            e = hypot(x - x0 / scale, y - y0 / scale)
        else:
            e = abs(y)

        errs.append(e)

    return {
        "series": errs,
        "min": min(errs),
        "max": max(errs),
        "start": errs[0],
        "end": errs[-1],
        "avg_step": (errs[-1] - errs[0]) / max(1, len(errs)),
    }

def report_drift(stats, steps_per_turn, turns):
    drift_per_turn = stats["avg_step"] * steps_per_turn
    print("\n=== DRIFT REPORT ===")
    print(f"turns:           {turns}")
    print(f"start error:     {stats['start']:.3e}")
    print(f"end error:       {stats['end']:.3e}")
    print(f"max error:       {stats['max']:.3e}")
    print(f"drift / turn:    {drift_per_turn:.3e}")


def report_phase_locked_drift_full(
    *,
    steps_per_turn: int,
    turns: int,
    total_steps: int,
    renorm_every: int,
    renorm_count: int,
    enable_turn_correction: bool,
    correction_gain_num: int,
    correction_gain_den: int,
    metric: str,
    drift_stats: dict,
    elapsed: float,
    boundary_errs_q: list | None = None
):
    err_start = drift_stats["start"]
    err_end   = drift_stats["end"]
    err_max   = drift_stats["max"]
    err_min   = drift_stats["min"]
    avg_step  = drift_stats["avg_step"]
    drift_turn = avg_step * steps_per_turn
    time_per_step_ns = (elapsed / total_steps) * 1e9 if total_steps else 0.0

    print("\n=== PHASE_LOCKED – DRIFT TEST (MANY TURNS) ===")
    print(f"steps/turn:              {steps_per_turn}")
    print(f"turns:                   {turns}")
    print(f"total steps:             {total_steps}")
    print(f"renorm_every:            {renorm_every}")
    print(f"renorm_count:            {renorm_count}")
    print(f"turn_correction:         {enable_turn_correction}  gain={correction_gain_num}/{correction_gain_den}")
    print(f"metric:                  {metric}")
    print(f"start error:             {err_start:.3e}")
    print(f"end error:               {err_end:.3e}")
    print(f"max error:               {err_max:.3e}")
    print(f"min error:               {err_min:.3e}")
    print(f"avg delta/step:          {avg_step:.3e}")
    print(f"drift per turn:          {drift_turn:.3e}")
    print(f"time total:              {elapsed:.6f} s")
    print(f"time/step:               {time_per_step_ns:.1f} ns")

    if enable_turn_correction and boundary_errs_q:
        avg_b = (sum(boundary_errs_q) / len(boundary_errs_q)) / FACTOR_SCALE
        max_b = (max(boundary_errs_q)) / FACTOR_SCALE
        print(f"boundary |y| (avg):      {avg_b:.3e}")
        print(f"boundary |y| (max):      {max_b:.3e}")