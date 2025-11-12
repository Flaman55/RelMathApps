# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# visualization.py — wykresy relacyjnej trygonometrii

import math
import matplotlib.pyplot as plt
from .constants import FACTOR_SCALE

def plot_with_accum_ref(xs_fixed, ys_fixed, accums_fixed):
    xs = [x / FACTOR_SCALE for x in xs_fixed]
    ys = [y / FACTOR_SCALE for y in ys_fixed]
    thetas = [a / FACTOR_SCALE for a in accums_fixed]
    refx = [math.cos(t) for t in thetas]
    refy = [math.sin(t) for t in thetas]

    fig, ax = plt.subplots(figsize=(6, 6))
    ax.plot(refx, refy, "--", label="ref (accum)")
    ax.plot(xs, ys, label="phase-locked")
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_title("Pełne kółko — referencja wg fazy (accum)")
    ax.grid(True); ax.legend(); fig.tight_layout(); plt.show()

def plot_benchmark(rows):
    steps = [r[0] for r in rows]
    max_err = [r[1] for r in rows]
    rms_err = [r[2] for r in rows]
    t_ns = [r[3] for r in rows]

    plt.figure()
    plt.plot(steps, max_err, marker="o", label="max ||p-pref||")
    plt.plot(steps, rms_err, marker="o", label="RMS ||p-pref||")
    plt.xlabel("Liczba kroków na 2π"); plt.ylabel("Błąd punktu")
    plt.title("Błąd punktu vs liczba kroków")
    plt.grid(True); plt.legend(); plt.tight_layout(); plt.show()

    plt.figure()
    plt.plot(steps, t_ns, marker="o")
    plt.xlabel("Liczba kroków na 2π"); plt.ylabel("ns/krok")
    plt.title("Czas generowania vs kroki")
    plt.grid(True); plt.tight_layout(); plt.show()
