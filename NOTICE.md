Relational Mathematics — Computational Framework  
Copyright (c) 2025 Artur Flaman (Flaman55)

All source code in this repository is provided under the
PolyForm Noncommercial License 1.0.0
(https://polyformproject.org/licenses/noncommercial/1.0.0/).

Free for noncommercial use in educational, research,
and private experimental contexts.

Commercial use or redistribution of modified versions
requires explicit written permission from the author.

Preferred attribution:
"Source: Relational Mathematics Project by Artur Flaman (Flaman55)"
https://relationalmathematics.org

## Third-party components

**libprimesieve** -- PrimeAtlas (number_theory/primeAtlas) generates prime numbers using
libprimesieve, an independent, third-party, open-source library.

Copyright (c) 2010 - 2026, Kim Walisch. All rights reserved.
Source: https://github.com/kimwalisch/primesieve
License: BSD 2-Clause License (see that repository's own `COPYING` file for the full text).

libprimesieve is used two ways within PrimeAtlas: (1) linked into this project's own C
sieve engines (`number_theory/primeAtlas/prime_sieve/prime_sieve_engine_v*.c`), which call
its internal segment-sieving functions as part of this project's own batching/orchestration
pipeline; and (2) called directly, via its own public C API
(`primesieve_generate_primes()`), by the "primesieve mode" Quick-generation option
(`number_theory/primeAtlas/prime_sieve/prime_sieve_primesieve.py`), with none of this
project's own engine code in between. No primesieve source code is copied into this
repository -- both integrations bind to a separately built/installed libprimesieve shared
library.
