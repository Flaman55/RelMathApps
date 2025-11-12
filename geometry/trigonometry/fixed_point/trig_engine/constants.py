# SPDX-License-Identifier: PolyForm-Noncommercial-1.0.0
# Copyright (c) 2025 Artur Flamandzki
# constants.py — stałe i konfiguracja arytmetyki Q1.60

FRAC_BITS = 60
FACTOR_SCALE = 1 << FRAC_BITS
ULP = 2.0 ** -FRAC_BITS
TWO_PI_FIXED = 7244019458077122560  # floor(2π * 2^60)
