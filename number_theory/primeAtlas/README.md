# PrimeAtlas

A desktop application for generating, browsing, and searching large-scale prime number
and prime-constellation (k-tuple) data. The GUI runs natively on Windows (tkinter);
the generation pipeline it drives runs under WSL, backed by `libprimesieve` and a set
of custom C sieve engines (two interchangeable engine generations, v3 and v4).

## Features

- **Prime numbers** -- browse generated data floor by floor (a digit-count range,
  floor `N` = `[10^N, 10^(N+1))`) and file by file, with per-floor and per-file prime
  counts, on-disk size, generation time, a paginated preview, and direct search for a
  specific value. A background worker computes floor totals (count + disk size)
  incrementally, so re-checking an already-scanned floor after a small change is cheap
  rather than a full rescan.
- **Constellations** -- browse detected k-tuple patterns floor by floor, with hit
  counts, offset/record metadata, a paginated preview that reconstructs each hit's
  full tuple, and a search that reports whether a given number participates in any
  recorded constellation.
- **Generation** -- two ways to launch the sieve/orchestrator pipeline and the
  constellation finder over WSL, both with live streamed output (stackable across
  runs, detachable into its own window) and a stop control:
  - **Quick generation** -- four simple modes (Floor only, Range from/to,
    Exploration, primesieve) that translate a plain request into the right low-level
    parameters, check what is already on disk first, and report "already in storage"
    instead of launching a redundant run. An "Auto" button estimates a safe window count
    from the WSL environment's available RAM (see "Window count, throughput, and RAM"
    below). See "The primesieve mode" below for how the fourth mode differs from the
    other three.
  - **Low-level form** -- exposes every CLI parameter of the orchestrator and
    constellation finder directly (workers, batch size, window count, window width,
    write-files toggle, sieving-prime count diagnostic) for full manual control.
- **Benchmark** -- a throughput chart (seconds per 10M generated vs. floor depth) plus
  a full benchmark log table, with one-click PDF export of both.
- **Settings** -- configurable storage location, and backup/restore/delete of the
  generated database, including manifest-based drift detection against what is
  actually on disk. Both the backup list and the incomplete-restores list have their
  own delete button, for pruning old backups or abandoned/paused restore jobs without
  touching the generated data itself. See "Restore" below for how a restore run is
  ordered and which engine it uses.

## Floor semantics

A "floor" is a digit-count range: floor `N` covers `[10^N, 10^(N+1))`. Generation works
in fixed-width windows (10,000,000 numbers by default); how a floor relates to that
window width falls into two regimes:

- **Floors 0-6** are each narrower than one window (floor 6 is only 9,000,000 numbers
  wide), and together span exactly `[1, 10,000,000)` -- one window's worth. Requesting
  any floor in this range generates and completes, in a single pass, every one of
  floors 0-6 that is not already on disk, each written to its own `10p{N}/` folder. A
  floor only partially covered by wherever the batch happens to end is left out
  entirely rather than written half-finished.
- **Floors 7 and up** are each an exact multiple of the window width (floor 7 = 9
  windows, floor 8 = 90 windows, and so on), so a window never straddles a floor
  boundary at this depth. Floor-only and Range requests are capped at the requested
  floor's own last window -- anything beyond that boundary is dropped, not silently
  written under the wrong floor's folder. Exploration mode is the one intentional
  exception: it is meant to march forward indefinitely across many windows without
  that cap, since deep, open-ended continuation is its whole purpose.

## The primesieve mode

Every other engine (Floor only, Range, Exploration -- all three ultimately run
`orchestrator_loop_v2.py` / `prime_sieve_v3.py` or `v4.py`) links a small custom C wrapper
around libprimesieve's *internal* segment-sieving functions, wrapped in this project's own
parallel batching/orchestration machinery (workers, batches, a shared mmap buffer -- see
"Window count, throughput, and RAM" below). **primesieve mode** is different: it calls
libprimesieve's own top-level public C API function, `primesieve_generate_primes()`,
directly -- no custom engine, no batching, no orchestrator in between (see
`prime_sieve/prime_sieve_primesieve.py`). It maps the result onto exactly the same on-disk
format and folder layout as every other engine, so a floor generated through this mode is
indistinguishable, from the rest of the application's point of view, from one generated any
other way.

The trade is libprimesieve's own domain limit: it operates on the `uint64_t` range, so
nothing above `primesieve_get_max_stop()` (currently `2**64 - 1` =
18,446,744,073,709,551,615, which falls in the middle of floor 19, not at a floor boundary)
can be generated this way. A request that would cross that ceiling is truncated to it --
the run still launches for whatever part of the request is reachable, and both the Quick
generation panel (before launching) and the console output (while running) explain the
truncation and point at Floor/Range/Exploration mode for anything past it, since those three
have no such ceiling (at the cost of being slower). A request entirely past the ceiling is
rejected outright before anything launches.

primesieve mode's Quick generation fields differ from the other three: instead of a From/To
range, it takes a Floor + From (starting point) + Width (window-count multiplier) -- the same
floor-relative navigation Floor-only mode uses, rather than Range mode's absolute pair. Its
own Auto button fills From with wherever that floor's storage currently ends (not a
RAM-based suggestion, since this mode has no RAM-driven reason to keep window count small --
see "Window count, throughput, and RAM" below), making it easy to see where a floor's
generated data currently stops and extend it without hand-computing the continuation point.
Because this mode never allocates the combined shared buffer the other three depend on, its
Width field is not capped at their RAM-driven limit of 1,000 -- it can request as many
windows in one run as libprimesieve's own `uint64_t` range allows.

libprimesieve is an independent, third-party, open-source project by Kim Walisch
(https://github.com/kimwalisch/primesieve, BSD 2-Clause License) -- see `NOTICE.md` for the
full attribution. The Quick generation panel shows this attribution directly whenever
primesieve mode is selected, not just in source comments.

## Window count, throughput, and RAM

This section is about Floor only, Range, and Exploration mode -- the three engines that run
through this project's own batching/orchestration pipeline. primesieve mode (see above) has
no such relationship: it makes one direct call into libprimesieve's own bulk-generation
function per run, with no batches, workers, or shared buffer of this project's own involved.

The Quick generation panel's window-count fields (and the low-level form's own) have a
direct, mechanical relationship to both how fast a run goes and how much RAM it needs.
Both effects trace back to the same design choice: one invocation of the sieve engine
processes a whole batch of adjacent windows as a single *combined range*, sieved into
one shared output buffer, rather than one window at a time.

**Why more windows per run means better throughput.** Splitting the combined range
across parallel workers is not done window-by-window -- it is split into a small,
*fixed* number of equal-cost batches (24 parallel processes x 2 batches each by
default = 48 batches, regardless of how many windows are being generated). Each batch
pays a real, measurable one-time setup cost inside the C engine (positioning
`libprimesieve`'s iterator to that batch's own starting point -- a "bootstrap" call).
That fixed overhead is paid exactly the same number of times whether the run covers 10
windows or 1,000: the more windows batched into one invocation, the more actual sieved
output that same fixed setup cost gets amortized over, so numbers-per-second throughput
improves as window count grows -- up to the point where something else becomes the
bottleneck.

**Why more windows per run means more RAM.** The combined range is sieved into one
single, shared, bit-packed buffer (one bit per candidate number -- prime or not),
allocated once before any worker process starts, so every worker writes directly into
the same physical memory instead of returning its own private copy. That buffer's size
is `window_count * window_width / 8` bytes, growing *linearly* with window count. This
is deliberately much cheaper than it used to be (earlier engine revisions gave every
worker its own private buffer, multiplying peak RAM by the worker count), but it is
still the hard ceiling: however much window count helps throughput, the whole combined
buffer for one run has to fit in RAM at once. The Quick-gen panel's "Auto" button reads
WSL's currently available memory and suggests a window count against exactly this
formula (using half the available RAM as a safety margin, since the buffer is not the
only thing using memory during a run) -- pushing window count past that estimate risks
an out-of-memory failure rather than a graceful slowdown.

In short: within whatever RAM is available, a larger window count is close to strictly
better for throughput; RAM is the only reason not to simply set it as high as possible.

## Restore

Restoring from a backup (Settings tab) regenerates whatever a saved manifest says should
exist but currently does not, as a checkpointed job that can be paused, resumed, or
cancelled and resumed again in a later session.

A restore run is ordered in two strict phases across every floor named in the diff, rather
than finishing one floor end-to-end before starting the next: every floor's missing prime
windows are restored first, in ascending floor order, before any floor's constellation hits
are touched. This ordering matters because the constellation finder reads a floor's own
`source_primes` files -- running it against a floor whose windows are not fully back yet
would either fail outright or silently record an incomplete hit set.

Floors 0-6 restore as a single combined pass, mirroring Quick generation's own low-floor
completion (see "Floor semantics" above): requesting any one of them fills every other
floor in 0-6 that is not already on disk in that same run, instead of launching once per
floor.

For a floor whose range fits entirely under libprimesieve's own ceiling (see "The
primesieve mode" above), restore uses primesieve mode -- the whole missing range in one
run, with no RAM-driven window-count chunking needed. Floors above that ceiling fall back
to the orchestrator pipeline, using a RAM-based automatic window count per run -- the same
formula behind Quick generation's own "Auto" button, re-evaluated fresh for each floor
rather than a fixed default.

## Architecture

```
prime_atlas_v1.py           GUI entry point (tkinter), five tabs listed above
primeatlas/                 backend package used by the GUI, no tkinter dependency
  app_settings.py           storage path configuration
  manifest.py                backup manifest / snapshot model
  backup_store.py            backup creation
  restore_job.py             restore from backup
  delete_manager.py          database deletion
  settings_tab.py            Settings tab controller
  generation_console.py      stacked/detachable live-output console used by both
                              Generation sections
  i18n.py                    translation loading
  locales/                   strings_en.json, strings_pl.json, app_settings.json
prime_sieve/                 sieve and orchestration pipeline (invoked via WSL)
  prime_sieve_v1.py          PGS1 output format, process-pool orchestration
  prime_sieve_v3.py          PGS2 output format, shared-memory mmap orchestration;
                              also implements low-floor completion (floors 0-6) and
                              the per-floor sieving-prime-count cache
  prime_sieve_v4.py          same as v3, plus an inlined fast-path modulo in the C
                              engine for the per-sieving-prime phase computation
  prime_sieve_primesieve.py  "primesieve mode" -- calls libprimesieve's own public C API
                              (primesieve_generate_primes()) directly via ctypes, no custom
                              engine or batching pipeline; see "The primesieve mode" above
  prime_sieve_engine_v1.c    C sieve core for prime_sieve_v1.py (ctypes)
  prime_sieve_engine_v3.c    C sieve core for prime_sieve_v3.py (ctypes)
  prime_sieve_engine_v4.c    C sieve core for prime_sieve_v4.py (ctypes)
  orchestrator_v3.py         single-run driver (SCRIPT_NAME selects v3 or v4)
  orchestrator_loop_v2.py    continuous-run driver
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
launched by the GUI. A small `.portal_totals_cache.json` file lives alongside the
generated data, caching each floor's prime count and on-disk size so the Prime numbers
tab does not have to re-read every file's header on every visit.

## Requirements

GUI:
- Windows
- Python 3 with the standard library (`tkinter` included)

Generation pipeline (only needed to generate new data; browsing existing data needs
only the GUI requirements above):
- WSL with a Linux distribution
- `gcc`, `libprimesieve` (headers and library) for building the C sieve engines
- Python 3 with `numpy` inside WSL
- For primesieve mode specifically: the libprimesieve *shared library* installed where
  `ctypes.util.find_library("primesieve")` (or a plain `libprimesieve.so` on the linker
  search path) can find it at runtime -- the same library the `-lprimesieve` build step
  below links against, just also needed as a runtime `.so`, not only at build time.

## Building the sieve engines

From WSL, inside `prime_sieve/`:

```
gcc -O3 -shared -fPIC prime_sieve_engine_v1.c -o prime_sieve_engine_v1.so -lprimesieve -lstdc++ -lm
gcc -O3 -shared -fPIC prime_sieve_engine_v3.c -o prime_sieve_engine_v3.so -lprimesieve -lstdc++ -lm
gcc -O3 -shared -fPIC prime_sieve_engine_v4.c -o prime_sieve_engine_v4.so -lprimesieve -lstdc++ -lm
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
