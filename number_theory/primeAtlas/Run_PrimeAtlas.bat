@echo off
setlocal

rem Run_PrimeAtlas.bat -- podwojny klik uruchamia prime_atlas_v1.py bez
rem recznego wpisywania komendy w terminalu. Przechodzi do folderu, w ktorym lezy ten
rem plik .bat (%~dp0), wiec dziala niezaleznie od tego, skad zostal odpalony (np. skrot
rem na Pulpicie). Sam prime_atlas_v1.py i tak liczy wlasne sciezki wzgledem swojego
rem __file__, wiec ta zmiana katalogu jest tylko po to, zeby "python prime_atlas_v1.py"
rem ponizej znalazl wlasciwy plik.

cd /d "%~dp0"

where python >nul 2>nul
if %errorlevel%==0 (
    python prime_atlas_v1.py
    goto :check
)

where py >nul 2>nul
if %errorlevel%==0 (
    py prime_atlas_v1.py
    goto :check
)

echo.
echo [BLAD] Nie znaleziono Pythona w PATH ^(ani "python", ani "py"^).
echo Zainstaluj Python albo dodaj go do zmiennej PATH.
pause
exit /b 1

:check
if not %errorlevel%==0 (
    echo.
    echo [PrimeAtlas zakonczyl sie bledem, kod %errorlevel%]
    pause
)

endlocal
