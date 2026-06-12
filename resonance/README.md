# Resonance — Functional Resonators and Quantum Hypothesis

Part of the [Relational Mathematics](https://relationalmathematics.org) framework.  
Related project page: [flamandzkiartur.com/projects/p18/](https://flamandzkiartur.com/projects/p18/)

---

## Overview

This module implements and tests the **resonance function model** introduced in the Resona project,
with a focus on the quantum energy hypothesis: can composite resonators model the energy spectra
of physical systems?

### Resonance function (extended form)

```
R_n(x, y) = 2 * x^n * y / (x^(2n) + y^2)
```

- Peak = **1** exactly at `y = x^n` (on-trajectory)
- `R_n + (1 - R_n) = 1` — structural closure, not normalization

### Generalized resonator

Replacing the constant `2` with `2 * f(x, y)` yields a **function evaluator**:

```
R_{n,f}(x, y) = 2 * f(x,y) * x^n * y / (x^(2n) + y^2)
```

On trajectory `y = x^n`:

```
R_{n,f}(x, x^n) = f(x, x^n)   -- exact, algebraic identity
```

A composite resonator `F = sum_k R_{n_k, f_k}` becomes a **trajectory-space analog of Shannon sampling**:
any function `f` sampled at grid `{x^{n_k}}` can be recovered via Gram matrix inversion (frame theory).

---

## Files

| File | Description |
|------|-------------|
| `quantum_resonance_test.py` | Full test suite: inverse problem, reconstruction, prime basis fitting, base search, generalized resonator demo |

---

## Tests performed

1. **Inverse problem** — for any spectrum `{E_k}`, find `n_k = log_x(E_k)` that encodes it exactly. Checks rational/integer structure.
2. **Reconstruction** — analytic verification: `R_{n_k}(x, E_k) = 1` (error < 1e-16).
3. **Forward / prime basis** — fit atomic spectra using prime-indexed resonators `{R_2, R_3, R_5, ...}` as basis (NNLS).
4. **Base search** — find `x` such that `x^{p_k} = E_k = 1/k^2` (consistent `x` would mean prime resonators encode hydrogen exactly).
5. **Generalized demo** — verify `R_{n,f}(x, x^n) = f(x, x^n)` for arbitrary `f`; frame reconstruction of `f` from trajectory samples.

---

## Key findings (R&D observation)

- Any spectrum can be encoded exactly: `n_k = log_x(E_k)` always works.
- For **hydrogen** (Bohr): `n_k = -2*log_2(k)` — integers only for `k = 2^m`. Prime exponents do not naturally encode hydrogen at any fixed `x`.
- For the **generalized resonator**: frame reconstruction (dual-frame coefficients via `A^{-1}`) achieves RMSE < 1e-4 at trajectory sample points.
- **Open question**: does a physical system exist whose spectrum is `{x^{p_k}}` for consecutive primes and fixed `x`? Such a system would be a direct realisation of the prime resonator structure.

---

## Usage

```bash
pip install numpy matplotlib scipy
python quantum_resonance_test.py          # interactive plots
python quantum_resonance_test.py --save   # save PNG files
python quantum_resonance_test.py --x 2.718   # use e as base
```

---

## License

See [LICENSE](../License) in the root of this repository.  
Author: Artur Flamandzki — [flamandzkiartur.com](https://flamandzkiartur.com)
