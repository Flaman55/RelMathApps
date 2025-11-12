# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki

from sympy import isprime, primerange, nextprime

def goldbach_constructive_incremental(N):
    """
    Konstrukcyjny algorytm Goldbacha (wersja inkrementalna).
    Wykorzystuje przyrostową aktualizację listy liczb pierwszych.
    Zwraca (N, p, q, P) gdzie N = p + q i p, q ≤ P.
    """
    if N % 2 != 0 or N < 4:
        raise ValueError("N musi być parzyste i >= 4")

    # startujemy od czubka >= N/2
    P = nextprime(N // 2 - 1)
    primes = list(primerange(2, P + 1))  # początkowa baza pierwszych

    while True:
        # budujemy parzyste różnice od czubka
        E = sorted([P - p for p in primes if (P - p) % 2 == 0])
        t = 2 * P - N  # offset

        # test dziury szczytowej
        if t == 2 and not isprime(P - 2):
            P = nextprime(P)
            if P > primes[-1]:
                primes.append(P)
            continue

        # najmniejsze dodatnie e1, e2
        e_nonzero = [e for e in E if e > 0]
        e1, e2 = (e_nonzero + [0, 0])[:2]

        # przypadek 1: domknięcie ogona
        if t >= e1 + e2:
            for p in primes:
                q = N - p
                if q <= P and isprime(q):
                    return (N, p, q, P)

        # przypadek 2: t w E
        if t in E:
            for p in primes:
                q = N - p
                if q <= P and isprime(q):
                    return (N, p, q, P)

        # przypadek 3: t w E+E
        Eset = set(E)
        for ei in E:
            if (t - ei) in Eset:
                for p in primes:
                    q = N - p
                    if q <= P and isprime(q):
                        return (N, p, q, P)

        # zwiększamy czubek przyrostowo
        P = nextprime(P)
        if P > primes[-1]:
            primes.append(P)

def goldbach_constructive_incremental_steps(N):
    """
    Konstrukcyjny algorytm Goldbacha (wersja inkrementalna z liczeniem kroków).
    Zwraca (N, p, q, P, steps), gdzie steps = ile razy zwiększano czubek P.
    """
    if N % 2 != 0 or N < 4:
        raise ValueError("N musi być parzyste i >= 4")

    P = nextprime(N // 2 - 1)
    primes = list(primerange(2, P + 1))
    steps = 0

    while True:
        E = sorted([P - p for p in primes if (P - p) % 2 == 0])
        t = 2 * P - N

        # test dziury szczytowej (Lemat 2)
        if t == 2 and not isprime(P - 2):
            P = nextprime(P)
            steps += 1
            if P > primes[-1]:
                primes.append(P)
            continue

        e_nonzero = [e for e in E if e > 0]
        e1, e2 = (e_nonzero + [0, 0])[:2]

        # przypadek 1: domknięcie ogona
        if t >= e1 + e2:
            for p in primes:
                q = N - p
                if q <= P and isprime(q):
                    return (N, p, q, P, steps)

        # przypadek 2: t w E
        if t in E:
            for p in primes:
                q = N - p
                if q <= P and isprime(q):
                    return (N, p, q, P, steps)

        # przypadek 3: t w E+E
        Eset = set(E)
        for ei in E:
            if (t - ei) in Eset:
                for p in primes:
                    q = N - p
                    if q <= P and isprime(q):
                        return (N, p, q, P, steps)

        # zwiększamy czubek przyrostowo
        P = nextprime(P)
        steps += 1
        if P > primes[-1]:
            primes.append(P)


def test_goldbach_with_steps(limit_even):
    """
    Sprawdza wszystkie parzyste liczby 4..limit_even.
    Wypisuje ile razy trzeba było zwiększyć P zanim znalazło się rozwiązanie.
    """
    results = []
    for N in range(4, limit_even + 1, 2):
        result = goldbach_constructive_incremental_steps(N)
        results.append(result)
        n, p, q, P, steps = result
        if (steps > 30):
            print(f"{N} = {p} + {q} (P={P}, zwiększeń P: {steps})")
    return results


# --- przykładowe testy ---
if __name__ == "__main__":
    # for N in [20, 50, 100, 200, 1000, 7468764]:
    #     print(goldbach_constructive_incremental(N))
    # for N in range(4, 50, 2):
    #     print(goldbach_constructive_incremental(N))
    test_goldbach_with_steps(100000)


