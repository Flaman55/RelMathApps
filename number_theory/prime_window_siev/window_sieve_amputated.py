def window_sieve(N):
    P_min = 2
    primes = [2]
    P_max = 2

    print(f"Start: baza = {primes}, okno = ({P_max}, {P_min * P_max}]")

    while True:
        L = P_max + 1
        R = P_min * P_max

        if L > N:
            break

        # przycinamy okno do N
        real_R = min(R, N)

        # oznaczamy liczby jako potencjalnie pierwsze
        window = {n: True for n in range(L, real_R + 1)}

        # eliminacja wielokrotności z istniejącej bazy
        for p in primes:
            start = ((L + p - 1) // p) * p
            for x in range(start, real_R + 1, p):
                window[x] = False

        # wszystkie liczby, które przeżyły – to nowa generacja liczb pierwszych
        new_primes = [n for n, ok in window.items() if ok]

        if not new_primes:
            # Brak nowych liczb pierwszych <= N
            break

        print(f"W oknie ({P_max}, {real_R}] nowe liczby pierwsze: {new_primes}")

        # aktualizacja bazy
        primes.extend(new_primes)
        new_P_max = new_primes[-1]   # największa pierwsza z okna

        # jeśli przekroczyła N – koniec
        if new_P_max > N:
            break

        P_max = new_P_max

        print(f"Nowe okno: ({P_max}, {P_min * P_max}]")

    print(f"\nZakończono. Pierwsze do {N}, Len: {len(primes)}: {sorted(primes)}")



if __name__ == "__main__":
    N = int(input("Podaj górną granicę N: "))
    window_sieve(N)
