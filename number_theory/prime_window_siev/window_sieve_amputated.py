def window_sieve_amputated(N, P_min):
    # Wszystkie prime < P_min usuwamy
    removed_primes = [p for p in [2,3,5,7,11,13,17,19,23,29] if p < P_min]

    # przestrzeń liczb, które W OGÓLE istnieją
    exists = {n: True for n in range(2, N+1)}

    # wywalamy wszystkie wielokrotności usuniętych pierwszych
    for p in removed_primes:
        for x in range(p, N+1, p):
            exists[x] = False

    # start algorytmu
    primes = [P_min]
    P_max = P_min

    print(f"Start: baza = {primes}, okno = ({P_max}, {P_min * P_max}]")
    print(f"Usunięte pierwsze: {removed_primes}\n")

    while True:
        L = P_max + 1
        R = P_min * P_max

        if L > N:
            break

        real_R = min(R, N)

        # tworzymy okno tylko z istniejących liczb
        window = {n: True for n in range(L, real_R + 1) if exists[n]}

        # usuwamy wielokrotności z obecnej bazy primes
        for p in primes:
            start = ((L + p - 1) // p) * p
            for x in range(start, real_R + 1, p):
                if x in window:
                    window[x] = False

        # to co przetrwa, to nowa generacja prime'ów
        new_primes = [n for n, ok in window.items() if ok]

        if not new_primes:
            print(f"W oknie ({P_max}, {real_R}] brak nowych liczb.")
            break

        print(f"W oknie ({P_max}, {real_R}] nowe liczby pierwsze: {new_primes}")

        primes.extend(new_primes)
        new_P_max = new_primes[-1]

        if new_P_max > N:
            break

        P_max = new_P_max

        print(f"Nowe okno: ({P_max}, {P_min * P_max}]\n")

    print(f"\nZakończono. Liczby pierwsze (w amputowanej arytmetyce) do {N}:")
    print(sorted(primes))
    print(f"Łącznie: {len(primes)}")


if __name__ == "__main__":
    N  = int(input("Podaj górną granicę N: "))
    P_min = int(input("Podaj minimalną liczbę pierwszą P_min: "))
    window_sieve_amputated(N, P_min)
