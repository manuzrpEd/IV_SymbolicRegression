#!/usr/bin/env bash
# Reruns every experiment stage behind README section 12, in order (REPLICATION.md, section 5.4). Linux, macOS, Git Bash.
# Every script skips the runs already in its output file, so the chain is resumable: after an interruption, run it again.
# To start from scratch, first run:   python replication/clear_results.py --yes      (or --move-to DIR)
# From a terminal:                     bash replication/run_all.sh
# Detached:                            nohup bash replication/run_all.sh > /dev/null 2>&1 &
# Progress: experiments/phase4/logs/run_all.out.log; each step writes experiments/phase4/logs/<step>.out.log and .err.log.
# About 40 hours on a 4-core laptop, one process per step. Phases 3 and 4 can instead be run as two shards side by side
# (REPLICATION.md, section 5.4); the later steps then continue from here.
set -u
cd "$(dirname "$0")/.."
PY=.venv/bin/python
[ -x "$PY" ] || PY=.venv/Scripts/python.exe
LOGS=experiments/phase4/logs
mkdir -p "$LOGS"

log() { echo "$(date '+%F %T') $*" >> "$LOGS/run_all.out.log"; }
step() {  # step <name> <script and arguments>: appends stdout and stderr to the step's logs; records a failure and goes on
    local name=$1; shift
    if ! "$PY" -u "$@" >> "$LOGS/$name.out.log" 2>> "$LOGS/$name.err.log"; then
        log "FAILED: $name (see $LOGS/$name.err.log); the chain continues, rerun this script to resume"
    fi
}

log "run_all started"
step fetch                 experiments/fetch_data.py
log "data fetched"

step phase2                experiments/phase2.py --part main
step phase2                experiments/phase2.py --part sensitivity
step phase2-report         experiments/phase2_report.py
log "phase 2 done"

step phase3                experiments/phase3.py
step phase3-report         experiments/phase3_report.py
log "phase 3 done"

step phase4-search         experiments/phase4.py --grid breadth nscale nomax cf
step phase4-headline       experiments/phase4.py --grid headline
step phase4-analysis       experiments/phase4_analysis.py --workers 8
step phase4-separation     experiments/phase4_analysis.py --separation --workers 8
step phase4-report         experiments/phase4_report.py
log "phase 4 done"

step phase5-inference      experiments/phase5_inference.py --workers 8
step phase5-split          experiments/phase5_split.py --workers 8
step phase5-identification experiments/phase5_identification.py --workers 8
step phase5-discrete       experiments/phase5_discrete.py
step phase5-report         experiments/phase5_report.py
log "phase 5 done"

step phase6-search         experiments/phase6_simulated.py --part search
step phase6-analyze        experiments/phase6_simulated.py --part analyze --workers 8
step phase6-report         experiments/phase6_simulated.py --part report
step phase6-ak             experiments/phase6_ak.py
step phase6-engel          experiments/phase6_engel.py --data data/engel95.csv
step phase6-engel-synthetic experiments/phase6_engel.py --synthetic
log "phase 6 done"

step phase7-search         experiments/phase7_budget.py --part search
step phase7-analysis       experiments/phase7_budget.py --part analyze --workers 8
step phase7-report         experiments/phase7_budget.py --part report
log "phase 7 done; all done"
