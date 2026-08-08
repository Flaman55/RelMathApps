# PrimeAtlas

A desktop application for generating, browsing, and searching large-scale prime number
and prime-constellation (k-tuple) data. The GUI runs natively on Windows (tkinter);
the generation pipeline it drives runs under WSL, backed by `libprimesieve` and a set
of custom C sieve engines.

## Features

- **Prime numbers** -- browse generated data floor by floor (an exponent range) and
  file by file, with counts, generation time, a paginated preview, and direct search
  for a specific value.
- **Constellations** -- browse detected k-tuple patterns floor by floor, with hit
  counts, offset/record metadata, a paginated preview that reconstructs each hit's
  full tuple, and a search that reports whether a given number participates in any
  recorded constellation.
- **Generation** -- launches the sieve/orchestrator pipeline and the constellation
  finder directly from the GUI over WSL, exposing every CLI parameter of both tools
  (workers, batch size, window count, etc.) with live streamed output and a stop
  control, instead of a hand-typed terminal invocation.
- **Benchmark** -- a throughput chart (seconds per 10M generated vs. floor depth) plus
  a full benchmark log table, with one-click PDF export of both.
- **Settings** -- configurable storage location, and backup/restore/delete of the
  generated database, including manifest-based drift detection against what is
  actually on disk.

## Architecture

```
prime_atlas_v1.py        GUI entry point (tkinter), five tabs listed above
primeatlas/               backend package used by the GUI, no tkinter dependency
  app_settings.py         storage path configuration
  manifest.py             backup manifest / snapshot model
  backup_store.py         backup creation
  restore_job.py          restore from backup
  delete_manager.py       database deletion
  settings_tab.py         Settings tab controller
  i18n.py                 translation loading
  locales/                strings_en.json, strings_pl.json
prime_sieve/               sieve and orchestration pipeline (invoked via WSL)
  prime_sieve_v1.py        PGS1 output format, process-pool orchestration
  prime_sieve_v3.py        PGS2 output format, shared-memory mmap orchestration
  prime_sieve_engine_v1.c  C sieve core for prime_sieve_v1.py (ctypes)
  prime_sieve_engine_v3.c  C sieve core for prime_sieve_v3.py (ctypes)
  orchestrator_v3.py       single-run driver
  orchestrator_loop_v2.py  continuous-run driver
  orchestrator_loop_helpers.py
constellation/
  constellation_finder_v1.py  k-tuple pattern search over generated prime data
  pattern_catalog_v1.py       catalog of supported k-tuple patterns
Run_PrimeAtlas.bat           launches the GUI, visible console (errors surfaced directly)
Run_PrimeAtlas_Hidden.vbs    launches the GUI with no console window
```

Generated data is stored under a folder named `CONSTELLATION_PORTAL` (the name predates
and is independent of the application's own name). By default this folder is created
next to `prime_atlas_v1.py`, so the application is self-contained regardless of where
its directory is placed on disk. The location can be overridden either through the
Settings tab or by setting the `CONSTELLATION_PORTAL_DIR` environment variable, which
the sieve, orchestrator, and constellation-finder scripts also read directly when
launched by the GUI.

## Requirements

GUI:
- Windows
- Python 3 with the standard library (`tkinter` included)

Generation pipeline (only needed to generate new data; browsing existing data needs
only the GUI requirements above):
- WSL with a Linux distribution
- `gcc`, `libprimesieve` (headers and library) for building the C sieve engines
- Python 3 with `numpy` inside WSL

## Building the sieve engines

From WSL, inside `prime_sieve/`:

```
gcc -O3 -shared -fPIC prime_sieve_engine_v1.c -o prime_sieve_engine_v1.so -lprimesieve -lstdc++ -lm
gcc -O3 -shared -fPIC prime_sieve_engine_v3.c -o prime_sieve_engine_v3.so -lprimesieve -lstdc++ -lm
```

Prebuilt `.so` files are included; rebuild if the WSL environment's glibc/architecture
differs from the one they were built on.

## Running

Double-click `Run_PrimeAtlas.bat` (visible console, useful for diagnosing startup
errors) or `Run_PrimeAtlas_Hidden.vbs` (no console window). Equivalently:

```
python prime_atlas_v1.py
```

Language (English/Polish) is set from the Settings tab and takes effect on restart.

## License

Distributed under the license at the repository root (`License`, PolyForm Noncommercial
1.0.0). See `NOTICE.md` for attribution requirements.
