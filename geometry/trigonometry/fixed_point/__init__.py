# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki

from trig_engine.engines.exe_adapter import run_engine_exe
from trig_engine import diagnostics, visualization, benchmark
from trig_engine import Phase_Locked_Engine, engine_cordic, engine_cordic_locked
from trig_engine import MQGK_Engine, MQGK_Engine_v1, MQGK_Engine_6284
from trig_engine import MQGK_Engine_6288_16, MQGK_Engine_629248_512
from trig_engine.engines.engine_factory import make_engine

# ============================================================
# WYBÓR SILNIKÓW (CZARNE SKRZYNKI – EXE)
# ============================================================
USE_EXE = False

ENGINE_EXE = "./trig_engine_cli.exe"
PHASE_LOCKED_EXE = Phase_Locked_Engine
CORDIC_EXE = engine_cordic

ENGINES_EXE = [
    {
        "name": "Phase-Locked Engine",
        "exe": ENGINE_EXE,
        "engine_type": "phase",
        "renorm_every": 256,
        "enable_turn_correction": True,
        "correction_gain_num": 1,
        "correction_gain_den": 1,
    },
    {
        "name": "CORDIC incremental",
        "exe": ENGINE_EXE,
        "engine_type": "cordic",
        "enable_turn_correction": True,
        "renorm_every": 0,
        "enable_turn_correction": False,
    },
]
ENGINES_PYTHON = [
    {
        "name": "Phase-Locked Engine",
        "engine": Phase_Locked_Engine.run_small_angle_engine,
        "engine_type": "phase",
        "renorm_every": 256,
        "enable_turn_correction": True,
        "correction_gain_num": 1,
        "correction_gain_den": 1,
    },
    {
        "name": "CORDIC incremental",
        "engine": engine_cordic_locked.run_small_angle_engine,
        "engine_type": "cordic",
        "renorm_every": 0,
        "enable_turn_correction": True,
    },
    {
        "name": "BQGK 628 (V1.0)",
        "engine": MQGK_Engine.run_mqgk_engine,  # Twój zaimportowany silnik 628
        "engine_type": "mqgk",
        "mode": "native",                   # Wymuszamy natywną rozdzielczość 628
        "mqgk_c": 628,                      # Jawna informacja o cyklu
        "renorm_every": 0,
        "enable_turn_correction": False,
        "correction_gain_num": 0,
        "correction_gain_den": 0,
    },
    {
        "name": "BQGK 6284 (V1.3)",
        "engine": MQGK_Engine_6284.run_mqgk_engine, # Twój zaimportowany silnik 6284
        "engine_type": "mqgk_6284",
        "mode": "adaptive",                   # Wymuszamy natywną rozdzielczość 6284
        "mqgk_c": 6284,                     # Jawna informacja o cyklu
        "renorm_every": 0,
        "enable_turn_correction": False,
        "correction_gain_num": 0,
        "correction_gain_den": 0,
    },
    {
        "name": "MQGK Engine V1",
        "engine": MQGK_Engine_v1.run_mqgk_engine,
        "engine_type": "mqgk v1",
        "renorm_every": 1,
        "enable_turn_correction": False,
        "correction_gain_num": 1,
        "correction_gain_den": 1,
        "substep_mode": "halfstep",
    },
    {
        "name": "MQGK Engine 8288 16-bit",
        "engine": MQGK_Engine_6288_16.run_mqgk_engine,
        "engine_type": "mqgk 6288_16",
        "renorm_every": 1,
        "enable_turn_correction": False,
        "correction_gain_num": 1,
        "correction_gain_den": 1,
        "substep_mode": "adaptive",
    },
    {
        "name": "MQGK Engine 929248 512-bit",
        "engine": MQGK_Engine_629248_512.run_mqgk_engine,
        "engine_type": "mqgk 629248_512",
        "renorm_every": 1,
        "enable_turn_correction": False,
        "correction_gain_num": 1,
        "correction_gain_den": 1,
        "substep_mode": "native",
    },
]

# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    # =========================================================
    # SINGLE RUN (inspection / sanity check)
    # =========================================================
    if USE_EXE:
        ENGINES = ENGINES_EXE
    else:
        ENGINES = ENGINES_PYTHON

    for cfg in ENGINES:
        name = cfg["name"]

        print(f"\n==============================")
        print(f" SINGLE RUN — {name}")
        print(f"==============================")

        if USE_EXE:
            result = run_engine_exe(
                cfg,
                n_steps=1024,
                turns=1,
                renorm_every=cfg["renorm_every"],
                enable_turn_correction=cfg["enable_turn_correction"],
                correction_gain_num=cfg.get("correction_gain_num", 1),
                correction_gain_den=cfg.get("correction_gain_den", 1),
                precompute=True,
                renorm_threshold_bits=40,
            )
        else:
            result = cfg["engine"](
                n_steps=1024,
                turns=1,
                renorm_every=cfg["renorm_every"],
                enable_turn_correction=cfg["enable_turn_correction"],
                correction_gain_num=cfg.get("correction_gain_num", 1),
                correction_gain_den=cfg.get("correction_gain_den", 1),
            )

        xs = result["xs"]
        ys = result["ys"]
        accums = result["accums"]
        stats = result["stats"]

        print(f"\n=== ENGINE STATS ({name}) ===")
        for k, v in stats.items():
            print(f"{k:24s}: {v}")

        diagnostics.report_errors(xs, ys, accums, stats)
        visualization.plot_with_accum_ref(xs, ys, accums, name)

    # ============================================================
    # LONG-TERM DRIFT TEST
    # ============================================================

    for cfg in ENGINES:
        name = cfg["name"]
        if cfg["engine_type"] == "mqgk":
            turns = 1000
        elif cfg["engine_type"] == "mqgk_6284":
            turns = 1000
        elif cfg["engine_type"] == "mqgk v1":
            turns = 1000
        elif cfg["engine_type"] == "phase":
            turns = 1000
        else:
            turns = 100

        if USE_EXE:
            engine_call = lambda **kw: run_engine_exe(cfg, **kw)
        else:
            engine_call = cfg["engine"]
        
        engine_cfg = dict(cfg)        # ← KLUCZOWE
        engine_cfg["engine"] = engine_call
        engine_cfg["name"] = name

        drift = benchmark.drift_test(
            engine_cfg=engine_cfg,
            steps_per_turn=1024,
            turns=turns,
            metric="radius",
        )

        visualization.plot_drift(
            drift["metrics"]["series"],
            title=f"Drift over many turns — {name}",
        )

    # ============================================================
    # COMPARATIVE BENCHMARK
    # ============================================================

    comparison = {}

    for cfg in ENGINES:
        name = cfg["name"]
        if cfg["engine_type"] == "mqgk":
            turns = 100
            steps_lst=(256, 512)
        elif cfg["engine_type"] == "mqgk_6284":
            turns = 100
            steps_lst=(256, 512)
        elif cfg["engine_type"] == "mqgk v1":
            turns = 100
            steps_lst=(256, 512)
        elif cfg["engine_type"] == "phase":
            turns = 100
            steps_lst=(128, 256, 512, 1000, 1024, 2048, 4096, 8192, 16384)
        else:
            turns = 100
            steps_lst=(128, 256, 512, 1000)

        if USE_EXE:
            engine_callable = lambda **kw: run_engine_exe(
                cfg,
                **kw
            )
        else:
            engine_callable = cfg["engine"]

        rows = benchmark.benchmark(
            engine_cfg={
                "engine": engine_callable,
                "name": name,
                "renorm_every": cfg["renorm_every"],
                "enable_turn_correction": cfg["enable_turn_correction"],
                "correction_gain_num": cfg.get("correction_gain_num", 1),
                "correction_gain_den": cfg.get("correction_gain_den", 1),
            },
            steps_list=steps_lst,
            turns_bench=turns,
        )

        comparison[name] = rows

        visualization.plot_benchmark(
            rows,
            title=f"{name} – benchmark",
        )

    benchmark.print_comparison_table(comparison)
