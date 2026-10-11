@echo off
rem Builds paper\main.pdf with MiKTeX: pdflatex, bibtex, pdflatex twice. Run from anywhere:  paper\build.cmd
rem MiKTeX (user install) is added to PATH for this session if it is not already there.
cd /d "%~dp0"
set MIKTEX=%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64
if exist "%MIKTEX%\pdflatex.exe" set PATH=%MIKTEX%;%PATH%
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build.log || goto :fail
bibtex main >> build.log || goto :fail
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log || goto :fail
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log || goto :fail
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log || goto :fail
echo built main.pdf
exit /b 0
:fail
echo build failed; see paper\build.log and paper\main.log
exit /b 1
