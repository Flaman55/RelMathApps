# Phase-Locked Engine (PLE) Q1.60 
### High-Precision Fixed-Point Oscillator for Embedded Systems

[PL] **Phase-Locked Engine (PLE) Q1.60** to propozycja silnika syntezy wektora rotacyjnego (Sin/Cos) zoptymalizowanego dla mikrokontrolerów ARM Cortex-M. Implementacja eliminuje kumulatywny dryf fazy typowy dla oscylatorów przyrostowych, stanowiąc wydajną alternatywę dla algorytmu CORDIC w systemach o ograniczonych zasobach.

[EN] **Phase-Locked Engine (PLE) Q1.60** is a rotational vector synthesis engine (Sin/Cos) optimized for ARM Cortex-M microcontrollers. This implementation eliminates cumulative phase drift common in incremental oscillators, serving as an efficient alternative to the CORDIC algorithm in resource-constrained systems.

---

## 📊 Technical Comparison / Porównanie Techniczne

| Parameter / Parametr | PLE Q1.60 | Standard CORDIC | Notes / Uwagi |
| :--- | :--- | :--- | :--- |
| **Execution Time / Czas** | **1266 ns** | 7255 ns | Measured on ARM Cortex-M4 |
| **Phase Drift / Dryf** | **0.000 (Locked)** | $3.2 \times 10^{-13}$ / rev | No accumulation over time |
| **Flash Usage / Flash** | **~4.5 KB** | ~8-12 KB | Including 64-bit math libs |
| **RMS Error / Błąd RMS** | **$4.2 \times 10^{-16}$** | $3.4 \times 10^{-16}$ | Double precision equivalent |

---

## 🛠 Design Principles / Zasady Projektowe

### [PL] Kluczowe mechanizmy:
* **DDA Phase Planner:** Zastosowanie algorytmu typu Bresenham do korygowania kroku fazy, co zapewnia matematyczną spójność pełnego obrotu $2\pi$.
* **Rounding Residuals Feedback:** Akumulacja i reiniekcja błędów zaokrągleń ($rx, ry$), co stabilizuje amplitudę i minimalizuje bias kwantyzacji.
* **Taylor 5-th Order Approximation:** Wykorzystanie wydajnych instrukcji mnożących procesora zamiast iteracyjnych przesunięć bitowych.
* **Deterministic Execution:** Brak instrukcji warunkowych w pętli rotacji oraz brak zależności od FPU.

### [EN] Key Mechanisms:
* **DDA Phase Planner:** Uses a Bresenham-like algorithm for phase step correction, ensuring mathematical consistency of the $2\pi$ cycle.
* **Rounding Residuals Feedback:** Accumulation and re-injection of rounding errors ($rx, ry$) to stabilize amplitude and minimize quantization bias.
* **Taylor 5-th Order Approximation:** Leverages efficient hardware multipliers instead of iterative bit-shifts.
* **Deterministic Execution:** Constant execution time with no branching in the rotation loop and no FPU dependency.



---

## 🎯 Applications / Zastosowania

* **Digital Signal Synthesis (DDS):** Stabilne generatory nośnej bez konieczności stosowania dużych tablic LUT.
* **Motor Control (FOC):** Szybkie wyliczanie transformat Parka/Clarke'a.
* **SDR (Software Defined Radio):** Miksery częstotliwości wymagające wysokiej czystości widmowej.
* **Power-Sensitive Systems:** Redukcja cykli CPU przekłada się na niższe zużycie energii na próbkę.



---

## 🚀 Quick Start (C Code)

```c
#include "q60_core.h"

PhaseLockedEngine eng;

int main(void) {
    // Initializing engine for 1024 steps per full rotation
    q60_engine_init(&eng, 1024);

    while(1) {
        // Compute next sample with phase-lock correction
        q60_engine_step(&eng);
        
        // Results in Q1.60 format
        int64_t s = eng.y; 
        int64_t c = eng.x;
    }
}