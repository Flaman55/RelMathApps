# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki

from trig_engine import engine, diagnostics, visualization, benchmark

if __name__ == "__main__":
    result = engine.run_small_angle_engine(n_steps=1028)
    diagnostics.report_errors(result["xs"], result["ys"], result["accums"])
    visualization.plot_with_accum_ref(result["xs"], result["ys"], result["accums"])

    rows = benchmark.benchmark([128, 256, 500, 1000, 2000])
    visualization.plot_benchmark(rows)
