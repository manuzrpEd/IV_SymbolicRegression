@echo off
rem Reruns every experiment stage behind README section 12, in order (REPLICATION.md, section 5.4). Windows.
rem Every script skips the runs already in its output file, so the chain is resumable: after an interruption, run it again.
rem To start from scratch, first run:   python replication\clear_results.py --yes      (or --move-to DIR)
rem From a terminal:                     replication\run_all.cmd
rem Detached, so it survives the terminal closing:
rem   powershell -Command "Start-Process cmd.exe -ArgumentList '/c','replication\run_all.cmd' -WindowStyle Hidden"
rem Progress: experiments\phase4\logs\run_all.out.log; each step writes experiments\phase4\logs\<step>.out.log and .err.log.
rem About 40 hours on a 4-core laptop, one process per step. Phases 3 and 4 can instead be run as two shards side by side
rem (REPLICATION.md, section 5.4); the later steps then continue from here.
cd /d "%~dp0.."
set LOGS=experiments\phase4\logs
if not exist %LOGS% mkdir %LOGS%
set PY=.venv\Scripts\python.exe
echo %date% %time% run_all started >> %LOGS%\run_all.out.log

%PY% -u experiments\fetch_data.py >> %LOGS%\fetch.out.log 2>> %LOGS%\fetch.err.log
echo %date% %time% data fetched >> %LOGS%\run_all.out.log

%PY% -u experiments\phase2.py --part main >> %LOGS%\phase2.out.log 2>> %LOGS%\phase2.err.log
%PY% -u experiments\phase2.py --part sensitivity >> %LOGS%\phase2.out.log 2>> %LOGS%\phase2.err.log
%PY% -u experiments\phase2_report.py > %LOGS%\phase2-report.out.log 2> %LOGS%\phase2-report.err.log
echo %date% %time% phase 2 done >> %LOGS%\run_all.out.log

%PY% -u experiments\phase3.py >> %LOGS%\phase3.out.log 2>> %LOGS%\phase3.err.log
%PY% -u experiments\phase3_report.py > %LOGS%\phase3-report.out.log 2> %LOGS%\phase3-report.err.log
echo %date% %time% phase 3 done >> %LOGS%\run_all.out.log

%PY% -u experiments\phase4.py --grid breadth nscale nomax cf >> %LOGS%\phase4-search.out.log 2>> %LOGS%\phase4-search.err.log
%PY% -u experiments\phase4.py --grid headline >> %LOGS%\phase4-headline.out.log 2>> %LOGS%\phase4-headline.err.log
%PY% -u experiments\phase4_analysis.py --workers 8 >> %LOGS%\phase4-analysis.out.log 2>> %LOGS%\phase4-analysis.err.log
%PY% -u experiments\phase4_analysis.py --separation --workers 8 >> %LOGS%\phase4-separation.out.log 2>> %LOGS%\phase4-separation.err.log
%PY% -u experiments\phase4_report.py > %LOGS%\phase4-report.out.log 2> %LOGS%\phase4-report.err.log
echo %date% %time% phase 4 done >> %LOGS%\run_all.out.log

%PY% -u experiments\phase5_inference.py --workers 8 >> %LOGS%\phase5-inference.out.log 2>> %LOGS%\phase5-inference.err.log
%PY% -u experiments\phase5_split.py --workers 8 >> %LOGS%\phase5-split.out.log 2>> %LOGS%\phase5-split.err.log
%PY% -u experiments\phase5_identification.py --workers 8 >> %LOGS%\phase5-identification.out.log 2>> %LOGS%\phase5-identification.err.log
%PY% -u experiments\phase5_discrete.py > %LOGS%\phase5-discrete.out.log 2> %LOGS%\phase5-discrete.err.log
%PY% -u experiments\phase5_report.py > %LOGS%\phase5-report.out.log 2> %LOGS%\phase5-report.err.log
echo %date% %time% phase 5 done >> %LOGS%\run_all.out.log

%PY% -u experiments\phase6_simulated.py --part search >> %LOGS%\phase6-search.out.log 2>> %LOGS%\phase6-search.err.log
%PY% -u experiments\phase6_simulated.py --part analyze --workers 8 >> %LOGS%\phase6-analyze.out.log 2>> %LOGS%\phase6-analyze.err.log
%PY% -u experiments\phase6_simulated.py --part report > %LOGS%\phase6-report.out.log 2> %LOGS%\phase6-report.err.log
%PY% -u experiments\phase6_ak.py > %LOGS%\phase6-ak.out.log 2> %LOGS%\phase6-ak.err.log
%PY% -u experiments\phase6_engel.py --data data\engel95.csv > %LOGS%\phase6-engel.out.log 2> %LOGS%\phase6-engel.err.log
%PY% -u experiments\phase6_engel.py --synthetic > %LOGS%\phase6-engel-synthetic.out.log 2> %LOGS%\phase6-engel-synthetic.err.log
echo %date% %time% phase 6 done >> %LOGS%\run_all.out.log

%PY% -u experiments\phase7_budget.py --part search >> %LOGS%\phase7-search.out.log 2>> %LOGS%\phase7-search.err.log
%PY% -u experiments\phase7_budget.py --part analyze --workers 8 >> %LOGS%\phase7-analysis.out.log 2>> %LOGS%\phase7-analysis.err.log
%PY% -u experiments\phase7_budget.py --part report > %LOGS%\phase7-report.out.log 2> %LOGS%\phase7-report.err.log
echo %date% %time% phase 7 done; all done >> %LOGS%\run_all.out.log
