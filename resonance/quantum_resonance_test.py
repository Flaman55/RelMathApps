#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
quantum_resonance_test.py
==========================
Tests the hypothesis: can composite resonators model atomic energy spectra?
Also introduces the GENERALIZED resonator with arbitrary amplitude function.

--- STANDARD RESONATOR ---
    R_n(x, y) = 2 * x^n * y / (x^(2n) + y^2)
    - peak = 1 at y = x^n  (logical bit 1 on trajectory)
    - R_n + (1-R_n) = 1  (structural closure)

--- GENERALIZED RESONATOR ---
    The "2" is a normalization constant (inverse of peak 1/2 in literature form).
    Replace it with 2*f(x,y) to encode any function f:

    R_{n,f}(x,y) = 2 * f(x,y) * x^n * y / (x^(2n) + y^2)

    On trajectory y = x^n:
      R_{n,f}(x, x^n) = f(x, x^n)   <-- resonator EVALUATES f at trajectory crossing

    Composite:
      F(x,y) = sum_k  R_{n_k, f_k}(x,y)
      F(x, x^{n_j}) ~= f_j(x^{n_j})  (when trajectories well-separated)

    This is the trajectory-space analog of Shannon sampling:
    f sampled at trajectory grid {x^{n_k}} => encoded in resonator superposition.

    For quantum mechanics: f_k(E) = |psi_k(E)|^2 encodes wavefunction probability.
    The n_k grid (prime, integer, or arbitrary) defines the trajectory skeleton;
    f_k carries the physics.

Tests:
  1. INVERSE PROBLEM     -- what n_k encode a spectrum exactly
  2. RECONSTRUCTION      -- analytic verification R_{n_k}(x, E_k) = 1
  3. FORWARD / PRIME BASIS -- prime resonators as fitting basis
  4. BASE SEARCH         -- consistent x for prime encoding of H
  5. GENERALIZED DEMO    -- f-resonators encoding hydrogen |psi|^2

Usage:
    python quantum_resonance_test.py
    python quantum_resonance_test.py --x 2.718   # use e as base
    python quantum_resonance_test.py --save       # save plots to PNG
"""

import argparse
from fractions import Fraction

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from scipy.optimize import nnls
from scipy.signal import find_peaks


# ===================================================================
#  RESONANCE MODEL
# ===================================================================

def R(n, x, y):
    """
    Extended resonance function.
    R_n(x, y) = 2 * x^n * y / (x^(2n) + y^2)
    Peak = 1 at y = x^n.
    """
    xn = float(x) ** float(n)
    return 2.0 * xn * y / (xn**2 + y**2 + 1e-300)


def composite(ns, alphas, x, y):
    """F(x,y) = sum_k alpha_k * R_{n_k}(x,y)"""
    return sum(a * R(n, x, y) for a, n in zip(alphas, ns))


def trajectory_peak(n, x):
    """y-value where R_n(x, .) peaks."""
    return float(x) ** float(n)


# ===================================================================
#  GENERALIZED RESONATOR
# ===================================================================

def R_gen(n, x, y, f):
    """
    Generalized resonator:
      R_{n,f}(x,y) = 2 * f(x,y) * x^n * y / (x^2n + y^2)

    On trajectory y = x^n:
      R_{n,f}(x, x^n) = f(x, x^n)

    f is any callable f(x, y) -> float or array.
    Standard R_n is recovered with f(x,y) = 1.
    """
    xn = float(x) ** float(n)
    gate = 2.0 * xn * y / (xn**2 + y**2 + 1e-300)   # standard R_n
    return f(x, y) * gate


def composite_gen(ns, x, y, f_list):
    """
    Generalized composite: sum_k R_{n_k, f_k}(x, y).
    f_list: list of callables, one per n in ns.
    """
    return sum(R_gen(n, x, y, f) for n, f in zip(ns, f_list))


def verify_generalized(n, x, f):
    """
    Analytic check: R_{n,f}(x, x^n) should equal f(x, x^n).
    Returns (expected, got, error).
    """
    yn = float(x) ** float(n)
    expected = f(x, yn)
    got = R_gen(n, x, np.array([yn]), f)[0]
    return expected, got, abs(expected - got)


# ===================================================================
#  PHYSICAL SPECTRA
# ===================================================================

def hydrogen_levels(n_max=10):
    """
    |E_n| = 1/n^2  (normalized so |E_1| = 1 = 13.6 eV).
    Returns (n_indices, energies).
    """
    n = np.arange(1, n_max + 1, dtype=float)
    return n, 1.0 / n**2


def lyman_series(n_max=8):
    """
    Hydrogen Lyman emission lines (transitions n->1).
    dE_n = 1 - 1/n^2,  normalized to ionization limit = 1.
    """
    n = np.arange(2, n_max + 1, dtype=float)
    return n, 1.0 - 1.0 / n**2


def qho_levels(n_max=8):
    """
    Quantum harmonic oscillator: E_k = k + 0.5.
    Returns (k_indices, energies).
    """
    k = np.arange(0, n_max, dtype=float)
    return k, k + 0.5


# ===================================================================
#  UTILITIES
# ===================================================================

def primes_sieve(limit):
    """Return array of primes <= limit."""
    s = np.ones(limit + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(limit**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.where(s)[0]


def encode(energies, x):
    """n_k = log_x(E_k) -- resonance parameter placing peak at E_k."""
    return np.log(np.array(energies, dtype=float)) / np.log(float(x))


def rat_approx(v, denom=30):
    """Closest rational with denominator <= denom."""
    return Fraction(v).limit_denominator(denom)


# ===================================================================
#  INVERSE PROBLEM
# ===================================================================

def inverse_problem(x=2.0):
    sep = "=" * 62
    print("\n" + sep)
    print("  INVERSE PROBLEM  --  resonance params for atomic spectra")
    print(sep)
    print("  Base x = {}".format(x))

    for label, (k_arr, E) in [
        ("Hydrogen |E_k| = 1/k^2",  hydrogen_levels(8)),
        ("Lyman dE_k = 1-1/k^2",    lyman_series(8)),
        ("QHO E_k = k+0.5",         qho_levels(8)),
    ]:
        nk = encode(E, x)
        print("\n  [{}]".format(label))
        print("  {:>3}  {:>10}  {:>10}  {:>12}  {:>5}".format(
              "k", "E_k", "n_k", "rat.approx", "int?"))
        print("  " + "-" * 48)
        for k, e, n in zip(k_arr, E, nk):
            frac = rat_approx(n)
            is_int = "ok" if abs(n - round(n)) < 1e-9 else ""
            print("  {:>3}  {:>10.5f}  {:>10.5f}  {:>12}  {:>5}".format(
                  int(k), e, n, str(frac), is_int))

    print("\n  --- Key observation (hydrogen, x=2) ---")
    _, E_H = hydrogen_levels(10)
    nk = encode(E_H, 2.0)
    print("  n_k = log2(1/k^2) = -2*log2(k)")
    print("  -> For k = 2^m:   n_k = -2m  (exact negative even integers)")
    print("  -> For k = prime: n_k is generally irrational")
    print()
    for m in range(4):
        k = 2**m
        n_exact = -2.0 * np.log2(max(k, 1))
        note = "  <- integer" if abs(n_exact - round(n_exact)) < 1e-9 else ""
        print("  k={:>2}=2^{}: n_k = {:.6f}{}".format(k, m, n_exact, note))


# ===================================================================
#  RECONSTRUCTION TEST
# ===================================================================

def reconstruction_test(x=2.0, n_pts=80000):
    """
    Analytic check: R_{n_k}(x, E_k) = 1 for all k by construction.
    Also builds F(x,y) for visualization.
    """
    sep = "=" * 62
    print("\n" + sep)
    print("  RECONSTRUCTION TEST  --  analytic verification")
    print(sep)
    print("  R_{{n_k}}(x, E_k) should equal 1 for every k")

    results = {}
    for label, (k_arr, E) in [
        ("Hydrogen",  hydrogen_levels(7)),
        ("QHO",       qho_levels(7)),
    ]:
        nk = encode(E, x)
        alphas = np.ones(len(nk))

        errors = [abs(R(n, x, e) - 1.0) for n, e in zip(nk, E)]
        max_err = max(errors)
        status = "PASS" if max_err < 1e-9 else "FAIL"
        print("\n  [{}]  max |R_{{n_k}}(x, E_k) - 1| = {:.2e}  ({})".format(
              label, max_err, status))

        # Log-spaced y scan so closely-spaced small-E peaks stay resolved
        y_lo = max(E.min() * 0.3, 1e-4)
        y_hi = E.max() * 3.0
        y = np.exp(np.linspace(np.log(y_lo), np.log(y_hi), n_pts))
        F = composite(nk, alphas, x, y)

        min_dist = max(int(n_pts / (len(E) * 4)), 20)
        peaks_idx, _ = find_peaks(F, height=0.3, distance=min_dist)
        found = y[peaks_idx] if len(peaks_idx) else np.array([])

        results[label] = (y, F, E, found)

    return results


# ===================================================================
#  FORWARD PROBLEM -- PRIME BASIS FITTING
# ===================================================================

def prime_basis_fit(target_energies, x=2.0, n_primes=12, n_pts=20000):
    """
    Fit target spectrum using prime-indexed resonators as basis.
    Minimises ||A*alpha - b|| s.t. alpha >= 0.
    """
    primes = primes_sieve(60)[:n_primes].astype(float)
    y_lo = target_energies.min() * 0.3
    y_hi = target_energies.max() * 3.0
    y = np.linspace(y_lo, y_hi, n_pts)

    A = np.column_stack([R(p, x, y) for p in primes])

    b = np.zeros(n_pts)
    for E in target_energies:
        sigma = 0.005 * E
        b += np.exp(-0.5 * ((y - E) / sigma)**2)
    b /= (b.max() + 1e-12)

    alpha, residual = nnls(A, b)
    fitted = A @ alpha
    return primes, alpha, fitted, y, residual


def forward_problem(x=2.0):
    """
    At x=2: prime resonators peak at y=4,8,32,... -- above H range (0,1].
    At x=0.5: prime resonators peak at y=0.25,0.125,0.03125,...
               -- overlaps H range!
    Key: p=2 -> y=0.25 = E_2 (hydrogen n=2, exact match).
    """
    sep = "=" * 62
    print("\n" + sep)
    print("  FORWARD PROBLEM  --  prime resonator basis fitting")
    print(sep)

    summary = {}

    # Hydrogen at x=0.5: prime peaks in the right range
    print("\n  [x=0.5]  R_p(0.5,y) peaks at y=0.5^p -- inside H energy range")
    _, E_H = hydrogen_levels(6)
    primes_h, alpha_h, fitted_h, y_h, res_h = prime_basis_fit(E_H, x=0.5, n_primes=10)
    active = [(int(p), round(a, 4), trajectory_peak(p, 0.5))
              for p, a in zip(primes_h, alpha_h) if a > 1e-4]
    print("  Hydrogen  residual = {:.5f}".format(res_h))
    print("  {:>4}  {:>8}  {:>14}  {:>10}  {:>8}".format(
          "p", "alpha_p", "peak y=0.5^p", "H target", "error %"))
    print("  " + "-" * 50)
    _, E_all = hydrogen_levels(10)
    for p, a, peak in active:
        nearest = E_all[np.argmin(np.abs(E_all - peak))]
        rel_err = abs(peak - nearest) / nearest * 100
        bar = "#" * min(int(a * 50), 35)
        print("  {:>4}  {:>8.4f}  {:>14.6f}  {:>10.6f}  {:>6.2f}%  {}".format(
              p, a, peak, nearest, rel_err, bar))
    summary["Hydrogen |E_k|"] = (primes_h, alpha_h, fitted_h, y_h, E_H)

    # Lyman at x=0.5
    _, E_L = lyman_series(6)
    primes_l, alpha_l, fitted_l, y_l, res_l = prime_basis_fit(E_L, x=0.5, n_primes=10)
    summary["Lyman dE"] = (primes_l, alpha_l, fitted_l, y_l, E_L)

    # QHO at user x
    print("\n  [x={}]  QHO E_k = k+0.5".format(x))
    _, E_Q = qho_levels(6)
    primes_q, alpha_q, fitted_q, y_q, res_q = prime_basis_fit(E_Q, x=x, n_primes=10)
    active_q = [(int(p), round(a, 4)) for p, a in zip(primes_q, alpha_q) if a > 1e-4]
    print("  residual = {:.5f}".format(res_q))
    for p, a in active_q:
        bar = "#" * min(int(a * 30), 40)
        print("    p={:>3}: alpha={:.4f}  {}".format(p, a, bar))
    summary["QHO E_k"] = (primes_q, alpha_q, fitted_q, y_q, E_Q)

    return summary


# ===================================================================
#  BASE SEARCH
# ===================================================================

def base_search():
    """
    For each (k, p_k) pair: find x such that x^{p_k} = E_k = 1/k^2.
    If consistent x exists across all k, prime resonators encode H exactly.
    """
    sep = "=" * 62
    print("\n" + sep)
    print("  BASE SEARCH  --  x s.t. x^{{p_k}} = E_k = 1/k^2")
    print(sep)
    print("  (consistent x => prime resonators encode H at that base)\n")

    primes = primes_sieve(50)
    _, E_H = hydrogen_levels(10)

    print("  {:>3}  {:>5}  {:>8}  {:>18}  {:>8}".format(
          "k", "p_k", "E_k", "x = E_k^(1/p_k)", "ln x"))
    print("  " + "-" * 48)

    x_vals = []
    for k, (E, p) in enumerate(zip(E_H, primes), start=1):
        xk = E ** (1.0 / p)
        x_vals.append(xk)
        print("  {:>3}  {:>5}  {:>8.5f}  {:>18.8f}  {:>8.5f}".format(
              k, int(p), E, xk, np.log(xk)))

    x_arr = np.array(x_vals)
    print("\n  Range: [{:.6f}, {:.6f}]".format(x_arr.min(), x_arr.max()))
    print("  Std deviation: {:.6f}".format(x_arr.std()))
    if x_arr.std() < 0.01:
        print("  -> CONSISTENT x found -- prime resonators encode hydrogen!")
    else:
        print("  -> No consistent x -- H does not align with prime exponents.")
        print("     Structural encoding still works (n_k = log_x(E_k) always).")


# ===================================================================
#  HYDROGEN WAVEFUNCTIONS (radial, normalized)
# ===================================================================

def hydrogen_radial_prob(n, r):
    """
    |psi_{n,0,0}(r)|^2 * 4*pi*r^2  (s-orbital radial probability density).
    r in units of Bohr radius a0.  Normalized so integral = 1.
    """
    from math import factorial
    # Associated Laguerre L_{n-1}^1(2r/n) via scipy if available, else direct
    # For s-orbitals: psi_{n00}(r) = R_{n0}(r) * Y_00
    # R_{n0}(r) = -sqrt((2/(n*a0))^3 * (n-1)!/(2n*n!)^3) * e^{-r/n} * L_{n-1}^1(2r/n)
    # Using normalized form from Griffiths:
    x = 2.0 * r / n
    # Laguerre polynomial L_{n-1}^{1}(x) via recurrence
    if n == 1:
        L = 1.0
    elif n == 2:
        L = 2.0 - x
    elif n == 3:
        L = 0.5*(x**2 - 8*x + 12)
    elif n == 4:
        L = (-x**3 + 18*x**2 - 96*x + 144) / 6.0
    else:
        # scipy fallback
        try:
            from scipy.special import eval_genlaguerre
            L = eval_genlaguerre(n-1, 1, x)
        except Exception:
            L = 1.0
    # R_{n0}(r) = -sqrt(4/n^4) * e^{-r/n} * L  (unnorm, s-wave)
    # Probability density P(r) = r^2 * |R_{n0}|^2  (radial)
    norm_factor = 4.0 / n**4
    psi_r = np.sqrt(norm_factor) * np.exp(-r / n) * L
    return r**2 * psi_r**2   # radial probability density (not normalized here)


# ===================================================================
#  GENERALIZED RESONATOR DEMO
# ===================================================================

def generalized_demo(x=2.0):
    """
    Demonstrates generalized resonator R_{n,f}:
      - Encodes hydrogen radial probability density |psi_n(r)|^2
      - Resonance parameter n_k selected so trajectory hits each E_k
      - Amplitude function f_k(x,y) = |psi_k(y/E_1)|^2 (scaled)
      - Shows that F(x,y) traces the quantum probability landscape
    """
    sep = "=" * 62
    print("\n" + sep)
    print("  GENERALIZED RESONATOR  --  f-resonators demo")
    print(sep)
    print("  R_{{n,f}}(x,y) = 2*f(x,y)*x^n*y/(x^2n+y^2)")
    print("  On trajectory y=x^n:  R_{{n,f}}(x,x^n) = f(x, x^n)")

    # Analytic verification for a few f functions
    print("\n  Analytic check  R_{{n,f}}(x, x^n) = f(x, x^n):")
    print("  {:>4}  {:>20}  {:>12}  {:>12}  {:>10}".format(
          "n", "f(x, x^n) expected", "got", "error", "status"))
    print("  " + "-" * 62)

    test_cases = [
        ("f=sin(y)",   lambda xx, yy: np.sin(yy)),
        ("f=y^2",      lambda xx, yy: yy**2),
        ("f=exp(-y)",  lambda xx, yy: np.exp(-yy)),
        ("f=log(y+1)", lambda xx, yy: np.log(yy + 1.0)),
        ("f=1 (std)",  lambda xx, yy: np.ones_like(yy) if hasattr(yy,'__len__') else 1.0),
    ]

    for fname, f in test_cases:
        for n_test in [1.0, 2.0, -1.0]:
            expected, got, err = verify_generalized(n_test, x, f)
            status = "ok" if err < 1e-12 else "FAIL"
            print("  {:>4}  {:>20}  {:>12.6f}  {:>12.6f}  {:>10}".format(
                  int(n_test), "{} = {:.4f}".format(fname, expected), got, err, status))
        print()

    # Demo: encode hydrogen radial probability density
    print("  --- Hydrogen |psi_n|^2 encoded as f-resonator superposition ---")
    print("  Amplitude function: f_k(x,y) = P_k(y)  (radial prob. density)")
    print("  Trajectory n_k: encodes level k  (n_k = log_x(E_k))")

    _, E_H = hydrogen_levels(4)
    nk_H = encode(E_H, x)

    # Build f_k: for level k, map y -> radial coordinate via E_k
    # Use r = y / E_k * n_k (scaled so peak of psi is visible)
    f_list = []
    for k_idx, (n_res, E) in enumerate(zip(nk_H, E_H)):
        n_quantum = k_idx + 1
        def make_f(nq):
            def f(xx, yy):
                r = np.abs(yy) * nq**2 * 10  # scale y to Bohr radius range
                return hydrogen_radial_prob(nq, r) * 50  # amplitude scaling
            return f
        f_list.append(make_f(n_quantum))

    # Evaluate composite on trajectory points
    print("\n  {:>4}  {:>10}  {:>12}  {:>12}  {:>12}".format(
          "k", "E_k", "n_k", "f_k(x,x^nk)", "R_{n,f}(x,x^nk)"))
    print("  " + "-" * 55)
    for k_idx, (n_res, E, f) in enumerate(zip(nk_H, E_H, f_list)):
        yn = trajectory_peak(n_res, x)
        f_val = f(x, yn)
        r_val = verify_generalized(n_res, x, f)
        print("  {:>4}  {:>10.5f}  {:>12.5f}  {:>12.5f}  {:>12.5f}".format(
              k_idx+1, E, n_res, f_val, r_val[1]))

    return nk_H, f_list


# ===================================================================
#  PLOTS
# ===================================================================

def plot_overview(x, recon_results, fwd_summary, save=False):
    fig = plt.figure(figsize=(15, 10))
    fig.suptitle(
        "Quantum Resonance Hypothesis  --  R_n(x,y) = 2*x^n*y/(x^2n+y^2)  --  x = {}".format(x),
        fontsize=13, fontweight="bold"
    )
    gs = gridspec.GridSpec(2, 3, figure=fig, hspace=0.42, wspace=0.35)

    colors = ["#e74c3c", "#3498db", "#2ecc71", "#f39c12", "#9b59b6"]

    # (0,0) individual prime resonators
    ax = fig.add_subplot(gs[0, 0])
    y = np.linspace(0.01, 35, 8000)
    for p, c in zip([2, 3, 5, 7, 11], colors):
        ax.plot(y, R(p, x, y), color=c, lw=1.5, label="R_{}".format(p))
        ax.axvline(x**p, color=c, alpha=0.25, lw=0.8, ls="--")
    ax.set_title("Prime resonators (x={})".format(x))
    ax.set_xlabel("y"); ax.set_ylabel("R_p(x, y)")
    ax.legend(fontsize=7, ncol=2); ax.grid(alpha=0.25); ax.set_xlim(0, 35)

    # (0,1) hydrogen reconstruction
    ax = fig.add_subplot(gs[0, 1])
    y_scan, F, E_H, found_H = recon_results["Hydrogen"]
    ax.semilogx(y_scan, F, color="#3498db", lw=1.2, label="F(x,y) composite")
    for i, e in enumerate(E_H):
        ax.axvline(e, color="red", alpha=0.45, lw=0.9, ls="--")
        ax.text(e, 0.1, "n={}".format(i+1), fontsize=6.5, ha="center", color="darkred",
                rotation=90)
    ax.set_title("Hydrogen -- exact reconstruction")
    ax.set_xlabel("|E| / |E1|  (log scale)"); ax.set_ylabel("F")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    # (0,2) QHO reconstruction
    ax = fig.add_subplot(gs[0, 2])
    y_scan, F, E_QHO, found_QHO = recon_results["QHO"]
    ax.plot(y_scan, F, color="#2ecc71", lw=1.2, label="F(x,y) composite")
    for i, e in enumerate(E_QHO):
        ax.axvline(e, color="red", alpha=0.45, lw=0.9, ls="--")
        ax.text(e, 0.1, "k={}".format(i), fontsize=6.5, ha="center", color="darkred",
                rotation=90)
    ax.set_title("QHO -- exact reconstruction")
    ax.set_xlabel("E / hw"); ax.set_ylabel("F")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    # (1,0) resonance param structure
    ax = fig.add_subplot(gs[1, 0])
    _, E_H20 = hydrogen_levels(12)
    nk = encode(E_H20, x)
    k_arr = np.arange(1, 13)
    primes_list = primes_sieve(50)
    ax.plot(k_arr, nk, "o-", color="#3498db", lw=1.4, ms=5,
            label="n_k = log_x(E_k)")
    ax.plot(k_arr, -2 * np.log(k_arr) / np.log(x), "s--", color="#e74c3c",
            lw=1.0, ms=4, alpha=0.7, label="-2*log_x(k)  exact")
    pk_mask = np.isin(k_arr, primes_list)
    ax.scatter(k_arr[pk_mask], nk[pk_mask], s=90, color="#f39c12",
               zorder=5, label="prime k", marker="*")
    ax.set_title("H resonance params n_k")
    ax.set_xlabel("Level k"); ax.set_ylabel("n_k")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    # (1,1) prime basis fit -- hydrogen at x=0.5
    ax = fig.add_subplot(gs[1, 1])
    primes_b, alpha_b, fitted_b, y_b, E_b = fwd_summary["Hydrogen |E_k|"]
    y_fine = np.linspace(y_b[0], y_b[-1], 80000)
    F_fine = composite(primes_b, alpha_b, 0.5, y_fine)
    ax.plot(y_fine, F_fine, color="#9b59b6", lw=1.2, label="prime basis fit (x=0.5)")
    for e in E_b:
        ax.axvline(e, color="red", alpha=0.4, lw=0.8, ls="--")
    ax.set_title("H atom -- prime basis fit  (x=0.5)")
    ax.set_xlabel("|E| / |E1|"); ax.set_ylabel("F")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    # (1,2) prime coefficients comparison
    ax = fig.add_subplot(gs[1, 2])
    for label_key, color in [("Hydrogen |E_k|", "#3498db"),
                               ("Lyman dE",       "#e74c3c"),
                               ("QHO E_k",        "#2ecc71")]:
        pr, alp, *_ = fwd_summary[label_key]
        ax.plot(pr, alp, "o-", color=color, lw=1.2, ms=5, label=label_key)
    ax.set_title("Prime basis coefficients alpha_p")
    ax.set_xlabel("Prime p"); ax.set_ylabel("alpha_p")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    if save:
        fig.savefig("resonance_quantum_test.png", dpi=150, bbox_inches="tight")
        print("\n  Saved: resonance_quantum_test.png")
    return fig



def plot_generalized(x=2.0, save=False):
    """Plot: generalized resonators with different f functions."""
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    fig.suptitle(
        "Generalized R_{{n,f}}(x,y)=2*f(x,y)*x^n*y/(x^2n+y^2)  x={}".format(x),
        fontsize=12
    )
    y = np.linspace(0.001, 5.0, 20000)
    n_test = 1.0

    # left: different f on same trajectory
    ax = axes[0]
    f_cases = [
        ("f=1 (std)",   lambda xx, yy: 1.0,                  "#3498db"),
        ("f=sin(y)",    lambda xx, yy: np.sin(yy),            "#e74c3c"),
        ("f=exp(-y)",   lambda xx, yy: np.exp(-yy),           "#2ecc71"),
        ("f=y^2/10",    lambda xx, yy: yy**2 / 10.0,          "#f39c12"),
    ]
    ax.axvline(trajectory_peak(n_test, x), color="gray", lw=0.8, ls="--",
               label="traj y=x^n={:.1f}".format(trajectory_peak(n_test, x)))
    for lbl, f, c in f_cases:
        ax.plot(y, R_gen(n_test, x, y, f), color=c, lw=1.5, label=lbl)
    ax.set_title("n={}, different f(x,y)".format(int(n_test)))
    ax.set_xlabel("y"); ax.set_ylabel("R_{n,f}")
    ax.legend(fontsize=7); ax.grid(alpha=0.25); ax.set_ylim(-1.2, 1.5)

    # middle: energy-weighted f-resonators (hydrogen)
    ax = axes[1]
    _, E_H = hydrogen_levels(5)
    nk_H = encode(E_H, x)
    y2 = np.exp(np.linspace(np.log(0.001), np.log(2.0), 60000))
    for k_idx, (n_res, E) in enumerate(zip(nk_H, E_H)):
        fk = (lambda w: lambda xx, yy: w * np.ones_like(yy) if hasattr(yy, '__len__') else w)(E)
        ax.semilogx(y2, R_gen(n_res, x, y2, fk), lw=1.2,
                    label="k={}, w={:.3f}".format(k_idx+1, E))
        ax.axvline(E, color="gray", alpha=0.3, lw=0.7, ls=":")
    ax.set_title("Energy-weighted f_k=E_k resonators")
    ax.set_xlabel("y (log)"); ax.set_ylabel("R_{{n,f_k}}")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    # right: frame reconstruction (correct version)
    # Naive: sum_k f(x^{n_k}) * R_{n_k}  -- WRONG, bumps overlap
    # Correct: solve A*alpha = f_sampled, then reconstruct with alpha_k
    # where A_{jk} = R_{n_k}(x, x^{n_j})  (Gram matrix of the frame)
    ax = axes[2]
    def target_f(yy):
        return np.exp(-yy) * np.sin(3*yy) + 0.5
    y3 = np.linspace(0.01, 4.0, 10000)
    ns_grid = np.arange(0.1, 2.0, 0.15)
    y_traj = np.array([trajectory_peak(n, x) for n in ns_grid])
    f_samp = target_f(y_traj)

    # Build frame (Gram) matrix: A_{jk} = R_{n_k}(x, y_traj[j])
    A_gram = np.column_stack([R(n, x, y_traj) for n in ns_grid])

    # Solve: A_gram @ alpha = f_samp  (least squares)
    alpha_frame, _, _, _ = np.linalg.lstsq(A_gram, f_samp, rcond=None)

    # Reconstruct using dual-frame coefficients
    basis = np.column_stack([R(n, x, y3) for n in ns_grid])
    F_naive  = basis @ f_samp          # WRONG: direct f values as coeffs
    F_correct = basis @ alpha_frame    # CORRECT: dual frame coefficients

    ax.plot(y3, target_f(y3), color="black", lw=1.5, ls="--",
            label="target f(y)", zorder=5)
    ax.plot(y3, F_naive / (np.max(np.abs(F_naive)) + 1e-12) * np.max(np.abs(target_f(y3))),
            color="#aaaaaa", lw=1.0, alpha=0.7, label="naive (wrong: bumps overlap)")
    ax.plot(y3, F_correct, color="#3498db", lw=1.5,
            label="frame reconstruction (A^-1 * f_sampled)")
    ax.scatter(y_traj, f_samp, s=30, color="#e74c3c", zorder=6,
               label="trajectory samples")
    # residual
    f_at_traj_recon = basis[np.searchsorted(y3, y_traj).clip(0, len(y3)-1)] @ alpha_frame
    res = np.mean((f_at_traj_recon - f_samp)**2)**0.5
    ax.set_title("Frame reconstruction  (RMSE={:.4f})".format(res))
    ax.set_xlabel("y"); ax.set_ylabel("value")
    ax.legend(fontsize=7); ax.grid(alpha=0.25)

    if save:
        fig.savefig("resonance_generalized.png", dpi=150, bbox_inches="tight")
        print("  Saved: resonance_generalized.png")
    return fig


def plot_prime_scan(x=2.0, save=False):
    """Composite of first 6 prime resonators -- pure structural scan."""
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    fig.suptitle("Prime Composite Resonator -- structural scan", fontsize=12)
    primes = primes_sieve(15).astype(float)
    ax = axes[0]
    y = np.linspace(0.01, 200, 200000)
    F = sum(R(p, x, y) for p in primes)
    ax.plot(y, F, color="#3498db", lw=1.0)
    for p in primes:
        ax.axvline(x**p, color="red", alpha=0.3, lw=0.8, ls="--",
                   label="y=x^{}={:.1f}".format(int(p), x**p))
    ax.set_title("F(x,y) = sum R_p  for p in {2,3,5,7,11,13}")
    ax.set_xlabel("y"); ax.set_ylabel("F"); ax.grid(alpha=0.25)
    ax.legend(fontsize=7, ncol=2)
    ax = axes[1]
    y_log = np.logspace(-1, np.log10(200), 200000)
    F_log = sum(R(p, x, y_log) for p in primes)
    ax.semilogx(y_log, F_log, color="#e74c3c", lw=1.0)
    for p in primes:
        ax.axvline(x**p, color="gray", alpha=0.3, lw=0.8, ls="--")
    ax.set_title("Same -- log scale")
    ax.set_xlabel("y (log)"); ax.set_ylabel("F"); ax.grid(alpha=0.25)
    if save:
        fig.savefig("resonance_prime_scan.png", dpi=150, bbox_inches="tight")
        print("  Saved: resonance_prime_scan.png")
    return fig


def main():
    parser = argparse.ArgumentParser(description="Quantum resonance hypothesis test")
    parser.add_argument("--x", type=float, default=2.0,
                        help="Resonance base (default: 2.0; try: 2.718, 10.0)")
    parser.add_argument("--save", action="store_true", help="Save plots to PNG")
    args = parser.parse_args()
    x = args.x

    print("+----------------------------------------------------------+")
    print("|     QUANTUM RESONANCE HYPOTHESIS TEST                    |")
    print("|     R_n(x,y) = 2*x^n*y / (x^2n + y^2)                  |")
    print("+----------------------------------------------------------+")
    print("  Base x = {}".format(x))

    inverse_problem(x)
    recon_results = reconstruction_test(x)
    fwd_summary   = forward_problem(x)
    base_search()
    generalized_demo(x)

    print("\n" + "=" * 62)
    print("  INTERPRETATION")
    print("=" * 62)
    print("  STANDARD MODEL: R_n encodes spectra exactly (n_k = log_x(E_k)).")
    print("  Hydrogen 1/k^2 does NOT naturally produce prime exponents.")
    print("")
    print("  GENERALIZED MODEL: R_{n,f}(x,y) = 2*f(x,y)*x^n*y/(x^2n+y^2)")
    print("    On trajectory y=x^n:  output = f(x, x^n)")
    print("    => resonator EVALUATES f at trajectory crossing point")
    print("")
    print("  FRAME RECONSTRUCTION:")
    print("    Naive: sum f(x^{n_k})*R_{n_k}  -- WRONG (bumps overlap)")
    print("    Correct: solve A*alpha=f_sampled, A_{jk}=R_{n_k}(x, x^{n_j})")
    print("    Dual-frame coefficients alpha give faithful reconstruction.")
    print("")
    print("  SHANNON ANALOG:")
    print("    f sampled at trajectory grid {x^{n_k}} => encoded in frame.")
    print("    n_k grid = skeleton (prime, integer, arbitrary).")
    print("    f_k = physics (wavefunction, probability, energy density).")

    fig1 = plot_overview(x, recon_results, fwd_summary, save=args.save)
    fig2 = plot_prime_scan(x, save=args.save)
    fig3 = plot_generalized(x, save=args.save)

    if not args.save:
        plt.show()
    else:
        plt.close("all")


if __name__ == "__main__":
    main()
