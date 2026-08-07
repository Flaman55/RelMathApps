' Run_PrimeAtlas_Hidden.vbs -- uruchamia Run_PrimeAtlas.bat w ukrytym oknie
' (styl 0), zeby przy zwyklym uzyciu (np. skrot na Pulpicie) nie bylo widac czarnej
' konsoli obok okna aplikacji przez caly czas jej dzialania.
'
' Podwojne klikniecie .bat odpala go w oknie cmd.exe, ktore czeka linijka po linijce na
' zakonczenie polecenia "python prime_atlas_v1.py" (patrz Run_PrimeAtlas.bat) -- to
' konsola samego cmd.exe, nie cos tworzonego przez Pythona, i pozostaje widoczna przez
' caly czas dzialania aplikacji.
'
' Ten .vbs to obchodzi: uruchamia TEN SAM .bat (bez zadnych zmian w nim) przez
' WScript.Shell.Run z jawnie ukrytym stylem okna (0), wiec zadna konsola nigdy sie nie
' pokazuje. Run_PrimeAtlas.bat zostaje nietkniety i dziala normalnie jako plan B --
' uruchom go BEZPOSREDNIO (nie przez ten .vbs), gdy trzeba zobaczyc pelny tekst bledu
' startu (np. Python nieznaleziony w PATH) w konsoli zamiast w oknie komunikatu ponizej.
'
' Skrot na Pulpicie / w Start Menu powinien celowac w TEN plik (.vbs), nie w .bat.
Set fso = CreateObject("Scripting.FileSystemObject")
Set WshShell = CreateObject("WScript.Shell")

scriptDir = fso.GetParentFolderName(WScript.ScriptFullName)
batPath = fso.BuildPath(scriptDir, "Run_PrimeAtlas.bat")

If Not fso.FileExists(batPath) Then
    MsgBox "Nie znaleziono pliku:" & vbCrLf & batPath, vbCritical, "PrimeAtlas"
    WScript.Quit 1
End If

cmd = """" & batPath & """"
' 0 = okno ukryte, True = czekaj na zakonczenie i zwroc kod wyjscia (potrzebne, zeby
' w ogole wiedziec, czy start sie nie udal -- z False Run() zwrocilby 0 natychmiast).
exitCode = WshShell.Run(cmd, 0, True)

If exitCode <> 0 Then
    MsgBox "PrimeAtlas zakonczyl sie bledem (kod " & exitCode & ")." & vbCrLf & vbCrLf & _
           "Uruchom Run_PrimeAtlas.bat bezposrednio (dwuklik), zeby zobaczyc " & _
           "szczegoly bledu w konsoli.", _
           vbExclamation, "PrimeAtlas"
End If
