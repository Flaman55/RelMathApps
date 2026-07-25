# -*- coding: utf-8 -*-
from math import sqrt, isfinite

def nested_value(N: float, depth: int, tail: float) -> float:
    """
    Computes the value of the nested radical for a given N, depth, and tail value.
    Iterates backward from the tail to the root: R_k = sqrt(1 + (N + k - 2) * R_{k+1}).
    """
    r = tail
    for k in range(depth, 0, -1):
        r = (1.0 + (N + k - 2.0) * r) ** 0.5
    return r

def design_nested(R):
    """
    Inversion of the nested radical structure.
    Given R = [R_1, R_2, ..., R_{d+1}], returns coefficients a[1..d] such that:
    R_1 = sqrt(1 + a_1*sqrt(1 + a_2*...sqrt(1 + a_d*R_{d+1})...)).
    Requirement: R_k > 0 for all k.
    """
    assert len(R) >= 2 and all(x > 0 for x in R)
    return [ (R[k]**2 - 1.0)/R[k+1] for k in range(len(R)-1) ]

def print_identity_chain(N: int, depth: int):
    """
    Demonstrates the recursive identity for the tail T* = N + depth.
    Prints all levels of the calculation: R_k should ideally equal N + k - 1.
    This validates the structural coherence of the Ramanujan-type radical.
    """
    Tstar = N + depth
    r = Tstar
    chain = [(depth+1, r, f"Tail T*={Tstar} (Expected: {N+depth})")]
    ok = True
    for k in range(depth, 0, -1):
        coef = N + k - 2
        r = (1 + coef * r)**0.5
        expected = N + k - 1
        chain.append((k, r, f"Expected: {expected}"))
        ok &= abs(r - expected) < 1e-12

    # Print the result chain from bottom to top (root)
    # Full float64 precision (17 significant digits) -- the double already
    # carries this precision internally, so there is no cost to displaying it.
    print(f"\n== Identity Chain (N={N}, depth d={depth}, tail T*={Tstar}) ==")
    for k, val, note in reversed(chain):
        print(f"R_{k:>2} = {val:.17f}   <- {note}")

    print("Conclusion: LHS=N = {:.17f}, RHS=R_1 = {:.17f}, Difference = {:.6e} {}".format(
        float(N), chain[depth][1], abs(chain[depth][1]-N), "[PASSED]" if ok else "[FAILED]")
    )

def solve_tail_for_equality(N: float, depth: int, tol: float = 1e-12):
    """
    Numerically finds the tail value T* >= 0 such that nested_value(N, depth, T*) == N.
    Uses bisection method to find the equilibrium point of the structural system.
    """
    a, fa = 0.0, nested_value(N, depth, 0.0) - N
    b = max(1.0, N)
    fb = nested_value(N, depth, b) - N
    
    # Expansion of the search interval if the sign hasn't changed
    it = 0
    while fa*fb > 0 and it < 60:
        b *= 2.0
        fb = nested_value(N, depth, b) - N
        it += 1
        
    # Bisection core
    for _ in range(100):
        m = 0.5*(a+b)
        fm = nested_value(N, depth, m) - N
        if abs(fm) < tol or (b-a) < 1e-14*(1+abs(m)):
            return m
        if fa*fm <= 0:
            b, fb = m, fm
        else:
            a, fa = m, fm
    return 0.5*(a+b)

def pretty_table_no_plots(N_list=(2,3,4,5), max_depth=10):
    """
    Comprehensive verification:
    1) Layer-by-layer identity for 'Tail = N + d'.
    2) Numerical solver comparison (T* vs N+d formula).
    3) Educational contrast: static (tail=0) vs. structural rolling approach.
    """
    # 1) Structural Identity Chain (Demonstrate for selected depths)
    for N in N_list:
        for d in (1,2,3,4,8,10):
            print_identity_chain(N, d)

    # 2) Solving for the tail and comparing with the N+d theoretical model
    # (full float64 precision -- 17 significant digits, the double's native precision)
    for N in N_list:
        print(f"\n== N = {N} (Solving for tail T* where RHS == N) ==")
        print(f"{'dpth':>4} | {'Numerical T*':>22} | {'N+d (Formula)':>22} | {'Computed RHS':>22} | |RHS-N|")
        for d in range(1, max_depth+1):
            T_num = solve_tail_for_equality(N, d, tol=1e-13)
            rhs = nested_value(N, d, T_num)
            print(f"{d:4d} | {T_num:22.17f} | {float(N+d):22.17f} | {rhs:22.17f} | {abs(rhs-N):.6e}")

    # 3) Educational Contrast (Finite Radical vs Structural Rolling)
    for N in (3,):
        print(f"\n== Convergence Comparison for N={N} ==")
        print(f"{'dpth':>4} | {'Tail=0 (Static)':>22} | {'Rolling (Structural)':>22}")
        for d in range(1, max_depth+1):
            from_scratch = nested_value(N, d, 0.0)
            r_roll = nested_value(N, d, N + d)
            print(f"{d:4d} | {from_scratch:22.17f} | {r_roll:22.17f}")

    # 4) Tail-independence check: unlike rolling (tail deliberately solved to hit N),
    # these tail policies are fixed rules that do NOT reference N at all. The point
    # is that the limit does not care about the tail policy -- only about the
    # coefficients a_k -- so every column below still converges to the same N.
    #
    # Note: the map T -> R_1^(d)(T) is monotone increasing in T, and T = N+d gives
    # R_1 = N exactly (the identity chain / rolling). So a tail policy stays below
    # N and approaches it monotonically only if T(d) <= N+d for every d; policies
    # growing faster than that (e.g. d^2, 2^d) overshoot N before settling back
    # down. The policies below all satisfy T(d) <= N+d for any N >= 2, so they are
    # guaranteed to approach N from below without ever exceeding it.
    for N in (3,):
        print(f"\n== Tail-Independence Check for N={N} ==")
        policies = {
            "T=0":     lambda d: 0.0,
            "T=1":     lambda d: 1.0,
            "T=d/2":   lambda d: d / 2.0,
            "T=sqrtd": lambda d: d ** 0.5,
            "T=d":     lambda d: float(d),
        }
        header = f"{'dpth':>4} | " + " | ".join(f"{name:>22}" for name in policies)
        print(header)
        for d in range(1, max_depth + 1):
            vals = [nested_value(N, d, pol(d)) for pol in policies.values()]
            print(f"{d:4d} | " + " | ".join(f"{v:22.17f}" for v in vals))

if __name__ == "__main__":
    # Execute primary verification tables
    pretty_table_no_plots(N_list=(2,3,4,5), max_depth=10)
    
    # Example 1: Classical Ramanujan Structure Test
    N, d = 5, 6
    R = [N + k for k in range(d)] + [N + d]
    print("\na_k Coefficients (Ramanujan-style):", [round(x,6) for x in design_nested(R)])

    # Example 2: Parametric Delta Variation Test
    L, Delta, d = 2.5, 0.3, 5
    R = [L + i*Delta for i in range(d)] + [L + d*Delta]
    print("a_k Coefficients (Delta-variation):", [round(x,6) for x in design_nested(R)])

    # Example 3: Prime Number Sequence Mapping
    primes = [5,7,11,13,17,19,23]  # Sequence R_1..R_{d+1}
    print("a_k Coefficients (Prime-based):", [round(x,6) for x in design_nested(primes)])