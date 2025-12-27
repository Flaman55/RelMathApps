# trig_engine/engines/exe_adapter.py
import subprocess
import json
from pathlib import Path

_THIS_DIR = Path(__file__).parent
ENGINE_EXE = (_THIS_DIR / "trig_engine_cli.exe").resolve()


def run_engine_exe(
    engine_cfg,
    *,
    n_steps,
    turns,
    renorm_every=0,
    enable_turn_correction=False,
    correction_gain_num=1,
    correction_gain_den=1,
    precompute=True,
    renorm_threshold_bits=40,
    **_ignored,
):
    """
    Black-box runner that behaves like an engine function.
    Accepts the same kwargs as run_small_angle_engine to stay drop-in compatible.
    """

    if not ENGINE_EXE.exists():
        raise FileNotFoundError(f"Engine EXE not found: {ENGINE_EXE}")

    # engine_type jest jawny w cfg (nie wyciągamy go z enable_turn_correction,
    # bo to jest inny parametr semantycznie)
    engine_type = engine_cfg.get("engine_type", "phase")

    cmd = [
        str(ENGINE_EXE),
        "--engine", str(engine_type),
        "--steps", str(int(n_steps)),
        "--turns", str(int(turns)),
    ]

    # Jeśli chcesz, możesz rozszerzyć engine_cli o te flagi.
    # Na razie adapter przyjmuje je tylko po to, żeby benchmark się nie wywalał.

    try:
        out = subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError as e:
        print("ENGINE EXECUTION FAILED")
        print("COMMAND:", " ".join(cmd))
        print("OUTPUT:\n", e.output)
        raise

    try:
        result = json.loads(out)
    except json.JSONDecodeError:
        print("ENGINE RETURNED INVALID JSON")
        print("RAW OUTPUT:\n", out)
        raise RuntimeError("Invalid JSON from engine EXE")

    # kontrakt wynikowy
    required = {"xs", "ys", "accums", "stats"}
    missing = required - result.keys()
    if missing:
        raise RuntimeError(f"Engine result missing keys: {missing}")

    # twarda kompatybilność: jeśli EXE nie zwróciło pól, dokładamy sensowne defaulty
    stats = result.get("stats", {})
    stats.setdefault("n_steps", int(n_steps))
    stats.setdefault("turns", int(turns))
    stats.setdefault("renorm_every", int(renorm_every))
    stats.setdefault("renorm_count", 0)
    stats.setdefault("turn_correction", bool(enable_turn_correction))
    stats.setdefault("correction_gain_num", int(correction_gain_num))
    stats.setdefault("correction_gain_den", int(correction_gain_den))
    result["stats"] = stats

    return result
