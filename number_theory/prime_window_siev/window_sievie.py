def window_sieve(N):
    P_min = 2
    primes = [2]
    P_max = 2

    print(f"Start: base = {primes}, window = ({P_max}, {P_min * P_max}]")

    while True:
        L = P_max + 1
        R = P_min * P_max

        if L > N:
            break

        # cut the window to N
        real_R = min(R, N)

        # mark numbers as potentially prime
        window = {n: True for n in range(L, real_R + 1)}

        # eliminate multiples from the existing base
        for p in primes:
            start = ((L + p - 1) // p) * p
            for x in range(start, real_R + 1, p):
                window[x] = False

        # all numbers that survived – the new generation of primes
        new_primes = [n for n, ok in window.items() if ok]

        if not new_primes:
            # no new primes ≤ N
            break

        print(f"In the window ({P_max}, {real_R}] new primes: {new_primes}")

        # update the base
        primes.extend(new_primes)
        new_P_max = new_primes[-1]   # largest prime in the window

        # if it exceeded N – stop
        if new_P_max > N:
            break

        P_max = new_P_max

        print(f"New window: ({P_max}, {P_min * P_max}]")

    print(f"\nFinished. Primes up to {N}, Len: {len(primes)}: {sorted(primes)}")


if __name__ == "__main__":
    N = int(input("Enter the upper bound N: "))
    window_sieve(N)
