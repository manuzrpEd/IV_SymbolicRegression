@echo off
rem Resumes the "Before the paper" jobs of README §11 after an interruption (reboot, sleep, closed laptop).
rem Every script skips what is already done, so this can be run any number of times. Run it from a terminal:
rem     experiments\resume_jobs.cmd
rem or detached, so it survives the terminal:
rem     powershell -Command "Start-Process cmd.exe -ArgumentList '/c','experiments\resume_jobs.cmd' -WindowStyle Hidden"
rem Progress: experiments\phase4\logs\*.out.log (resume.out.log lists the steps as they finish).
cd /d "%~dp0.."
set LOGS=experiments\phase4\logs
if not exist %LOGS% mkdir %LOGS%
set PY=.venv\Scripts\python.exe
echo %date% %time% resume started >> %LOGS%\resume.out.log

%PY% -u experiments\phase4.py --grid headline >> %LOGS%\headline.out.log 2>> %LOGS%\headline.err.log
echo %date% %time% headline searches done >> %LOGS%\resume.out.log
%PY% -u experiments\phase4_analysis.py --workers 8 >> %LOGS%\analysis-headline.out.log 2>> %LOGS%\analysis-headline.err.log
%PY% -u experiments\phase4_report.py > %LOGS%\report-headline.out.log 2> %LOGS%\report-headline.err.log
echo %date% %time% phase4 analysis and report done >> %LOGS%\resume.out.log

%PY% -u experiments\phase7_budget.py --part search >> %LOGS%\budget-search.out.log 2>> %LOGS%\budget-search.err.log
%PY% -u experiments\phase7_budget.py --part analyze --workers 8 >> %LOGS%\budget-analysis.out.log 2>> %LOGS%\budget-analysis.err.log
%PY% -u experiments\phase7_budget.py --part report > %LOGS%\budget-report.out.log 2> %LOGS%\budget-report.err.log
echo %date% %time% budget experiment done >> %LOGS%\resume.out.log

%PY% -u experiments\phase5_identification.py --workers 8 --recompute > %LOGS%\identification-recompute.out.log 2> %LOGS%\identification-recompute.err.log
%PY% -u experiments\phase5_report.py > %LOGS%\p5report-recompute.out.log 2> %LOGS%\p5report-recompute.err.log
%PY% -u experiments\phase6_simulated.py --part analyze --workers 8 --recompute > %LOGS%\phase6-analyze-recompute.out.log 2> %LOGS%\phase6-analyze-recompute.err.log
%PY% -u experiments\phase6_simulated.py --part report > %LOGS%\phase6-report-recompute.out.log 2> %LOGS%\phase6-report-recompute.err.log
echo %date% %time% diagnostics recomputed; all done >> %LOGS%\resume.out.log
