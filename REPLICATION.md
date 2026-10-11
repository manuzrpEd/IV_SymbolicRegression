# Replication guide

Symbolic regression under endogeneity: formula search scored by instrumental-variable moment conditions.
This document is written for referees, data editors and anyone who wants to re-run the computations behind
[README.md](README.md) §12 and [THEORY.md](THEORY.md) §7. It states where every number comes from, what is needed
to recompute it, how long that takes, and which parts reproduce exactly and which only in distribution.

Everything reported was produced by the scripts in this repository between 2026-09-30 and 2026-10-02 on one laptop
(§3.2). Every result file is committed under `experiments/phase*/`, and none was edited by hand: the summaries are
written by the report scripts from the run records, and README §12 quotes those summaries.

Two checks are possible, and both are described in §5:

- **Check A, recompute from the saved searches** (about 5 hours, deterministic). Every symbolic-regression search
  saved its Pareto front. Everything downstream of the fronts (constant refits, selection, metrics, the identification
  diagnostic, the inference simulations, the reports and figures) is pure Python with fixed seeds, and rerunning it
  must give the committed files byte for byte (§5.3 says what was verified).
- **Check B, rerun from scratch** (about 40 hours of compute). The searches themselves are stochastic (§3.4), so
  Check B reproduces the recovery rates in distribution, within the intervals printed in each summary, and the
  data-only statistics exactly.

Contents: 1 Package · 2 Data · 3 Requirements (software, hardware, runtime, randomness) · 4 Code · 5 Instructions ·
6 Tables and figures · 7 Inventory · 8 Known issues · 9 Licence and contact.

---

## 1. What the package contains

| Path | Content |
|---|---|
| `src/symiv/` | The method: data-generating processes, instrument bases and the GMM criterion, the PySR wrappers and the Julia loss, two-step GMM refits, selection rules, recovery and error metrics, the identification diagnostic, the template library, the baselines. |
| `experiments/*.py` | One script per experiment stage (§4). Each writes one JSON line per run and a Markdown summary. |
| `experiments/phase2/` … `phase7/` | The run records (`*.jsonl`, `*.json`), the summaries (`*.md`) and the two figures (`*.png`) that README §12 quotes (§7 lists them with record counts). |
| `tests/` | 97 pytest tests: 94 pure-Python tests run by default, 2 PySR integration tests (marker `julia`) and 1 DeepIV training test (marker `slow`). |
| `README.md`, `THEORY.md` | The research plan with results (§12) and the theory with proofs and a referee log. |
| `replication/requirements-frozen.txt` | The exact Python environment of the reported runs (`pip freeze`). |
| `replication/julia/Project.toml`, `Manifest.toml` | The exact Julia environment that PySR installed (SymbolicRegression.jl 2.5.1 and its dependency tree). |
| `replication/checksums.sha256` | SHA-256 of every committed result file, to check a download is intact. |
| `replication/clear_results.py` | Removes or moves aside the committed results so a rerun starts from scratch (§5.4). |
| `replication/run_all.cmd`, `run_all.sh` | The whole chain of §5.4 in order, Windows and POSIX. |
| `experiments/resume_jobs.cmd` | Resumes the last compute chain after an interruption (Windows). |
| `data/` | Not in git. The two public application files, downloaded by `experiments/fetch_data.py` (§2). |

---

## 2. Data availability and provenance

**Simulated data (README §12.1 to §12.4, §12.6, and the simulated environments of §12.5).** All samples are generated
by `symiv.dgp.simulate(design, law, n, seed)` from the designs D1 to D6 and the laws defined in `src/symiv/dgp/`
(README §8.1 and §8.2). No external data enter these sections. The draws use NumPy's `default_rng(seed)`; §3.4 says
what that guarantees.

**Two public third-party files (README §12.5, §8.3).** Both are downloaded by `python experiments/fetch_data.py`
into `data/` (git-ignored; needs the `apps` extra). Neither is redistributed with the repository: the Angrist–Krueger
file carries no licence statement, and the Engel file is kept out for consistency and because its conversion is
scripted. The author has legitimate access to both; they are public and contain no confidential information.

| File | Source | Content | Size and SHA-256 |
|---|---|---|---|
| `data/ak91.dta` | Angrist and Krueger (1991) 1980 Census extract as distributed on Angrist and Pischke's *Mastering 'Metrics* site: `https://www.masteringmetrics.com/wp-content/uploads/2015/02/ak91.dta` | 329,509 men born 1930–39; columns `lnw`, `s`, `yob`, `qob`, `sob` | 6,591,291 bytes; `e86e13e48a4241ab8ae5e3ff827cf2e07bf0a514f143ccfdf0a82d270a79a79e` |
| `data/np_0.70-5.tar.gz` | CRAN source tarball of the R package **np** 0.70-5 (licence GPL), `https://cran.r-project.org/src/contrib/np_0.70-5.tar.gz`, or `.../src/contrib/Archive/np/np_0.70-5.tar.gz` once a newer np is on CRAN | contains `np/data/Engel95.rda` | 1,612,910 bytes; `dc31f4e3f921eab2b60b15ca0d4cc378e24e315b8231658cd6f47ad29a818584` |
| `data/engel95.csv` | `Engel95.rda` read with pyreadr and written as CSV by `fetch_data.py` | Blundell, Chen and Kristensen's (2007) FES 1995 sample: 1,655 married couples; columns `food`, `catering`, `alcohol`, `fuel`, `motor`, `fares`, `leisure`, `logexp`, `logwages`, `nkids` | 277,955 bytes; `0177667861c981f33198d254acc7c21767a75c23f2a4e6e22878ea1b8206c764` |

If a URL has moved, obtain the same file from the source named above, place it in `data/` under the same name, and
compare its SHA-256 with the table (`sha256sum data/ak91.dta`, or `Get-FileHash data\ak91.dta` in PowerShell).
`fetch_data.py --np-version X` fetches another np version; the CSV checksum above applies to the Engel95 frame as
shipped in np 0.70-5, so after a version change compare the row count (1,655) and the columns instead.

---

## 3. Computational requirements

### 3.1 Software

| Component | Version used | How it is pinned |
|---|---|---|
| Python | 3.12.10 (64-bit) | `pyproject.toml` requires ≥ 3.10 |
| numpy, scipy, sympy, scikit-learn | 2.5.3, 1.18.1, 1.14.0, 1.9.1 | `replication/requirements-frozen.txt` |
| pysr, juliacall, juliapkg | 2.6.0, 0.9.36, 0.1.27 | same |
| matplotlib (figures), pandas and pyreadr (data files), pytest | 3.11.2, 3.0.6, 0.5.7, 9.1.1 | same |
| torch (DeepIV baseline, Phase 3 only) | 2.14.1+cpu | same; CPU build from `https://download.pytorch.org/whl/cpu` |
| Julia | 1.11.9 | installed by juliapkg into `.venv/julia_env/pyjuliapkg/` at the first `import pysr` |
| SymbolicRegression.jl | 2.5.1 | PySR 2.6.0 asks for `~2.5.0` and juliapkg resolves the newest 2.5.x; `replication/julia/Manifest.toml` records the exact tree |
| PythonCall.jl | 0.9.36 | pinned by juliacall |
| Operating system | Windows 11 Pro 10.0.26300 | the code is plain Python and runs on Linux and macOS; only the detached-job commands in §5.4 are platform-specific |

`pyproject.toml` declares lower bounds only. The frozen file reproduces the environment exactly; a newer environment
within those bounds is expected to work and to give the same downstream numbers, with the caveat on NumPy in §3.4.

**Pinning the Julia side exactly.** The reported results do not depend on it (the search is stochastic in any case,
and everything after the search is Python), but two mechanisms exist. (a) After the first `import pysr` has created
`.venv/julia_env/`, add a pin to the environment's own dependency file, which juliapkg always reads, and import again:

```
python -c "import juliapkg; juliapkg.add('SymbolicRegression', '8254be44-1295-4e6a-a16d-46603ac705cb', version='=2.5.1')"
python -c "import pysr"
```

The first line writes `.venv/julia_env/pyjuliapkg/juliapkg.json`; juliapkg re-resolves whenever a dependency file
changes, so the second line installs exactly 2.5.1. (b) Copy `replication/julia/Manifest.toml` over
`.venv/julia_env/Manifest.toml` and run
`.venv/julia_env/pyjuliapkg/install/bin/julia --project=.venv/julia_env -e "using Pkg; Pkg.instantiate()"`.
Mechanism (a) was checked against juliapkg's source and by writing the pin file to a scratch location; neither
mechanism was used for the reported runs, which took the versions juliapkg resolved on 2026-09-30.

### 3.2 Hardware used

One laptop: Intel Core i7-1165G7 (4 cores, 8 threads, 2.8 GHz), 32 GB RAM, SSD, no GPU. The analysis scripts use
8 worker processes (`--workers 8`); peak memory was not measured, and no step was memory-bound on this machine.
Disk: the committed results are 41 MB, the two data files 8 MB; the virtual environment is 2.1 GB, of which Julia,
SymbolicRegression.jl and their compiled caches are 1.0 GB.

### 3.3 Runtime, as measured

Search times are the sums of the per-run times stored in the run records (`times` fields) or printed in the job
logs; wall times are from the log timestamps. "Shards" means two processes run side by side with
`PYTHON_JULIACALL_THREADS=4` each.

| Step | Runs | Compute time | As run |
|---|---|---|---|
| Phase 2, `phase2.py --part main` and `--part sensitivity` | 280 | 2.4 h of search (2.1 h symbolic IV, 0.2 h plain PySR) | one process, about 2 h + 45 min |
| Phase 3, `phase3.py` | 300 | 8.0 h summed over the 15 methods | two shards, about 4 h wall |
| Phase 4, `phase4.py --grid breadth nscale nomax cf` | 528 | 11.8 h of search | two shards, about 6 h wall |
| Phase 4, `phase4.py --grid headline` | 570 | 8.2 h of search | one process, 8 h 9 min wall |
| Phase 4, `phase4_analysis.py --workers 8` | 1,098 fronts | about 2 h 20 min in total | 8 workers |
| Phase 4, `phase4_analysis.py --separation --workers 8` | 523 lines | about 25 min | 8 workers |
| Phase 5, `phase5_inference.py`, `phase5_split.py` | 4,500 and 672 rows | a few minutes each (not logged) | 8 workers |
| Phase 5, `phase5_identification.py --workers 8` | 630 | 15 min | 8 workers |
| Phase 5, `phase5_discrete.py` | 8 fits | 2 s | |
| Phase 6, `phase6_simulated.py` (search, analyze, report) | 140 | 20 min of search + 12 min of analysis | |
| Phase 6, `phase6_ak.py` | 2 instrument sets | 15 min | |
| Phase 6, `phase6_engel.py --data data/engel95.csv` | 21 | 13 min of search + 3 min of selection and tests | |
| Phase 6, `phase6_engel.py --synthetic` | 1 | 5 min | |
| Phase 7, `phase7_budget.py` (search, analyze, report) | 88 runs × 2 restarts, 352 analyses | 3 h 20 min of search + 1 h 26 min of analysis | |
| Every report script | | seconds | |
| `pytest` / `pytest -m julia` / `smoke_pysr.py` | 94 / 2 / 1 | 20 s / about 1 min / about 6 min (two searches of about 2.5 min each plus Julia's start-up) | |

In total about 40 hours of compute; about 30 hours of wall time with two shards for Phases 3 and 4. Check A
(§5.3) needs about 5 hours of it, almost all in the Phase 4 and Phase 7 analyses.

### 3.4 Randomness: what reproduces exactly

**Samples.** Every simulated sample is drawn by `np.random.default_rng(seed)` (PCG64) inside `symiv.dgp`, with the
seeds listed below, so the data of every run are reproducible from the run's key. NumPy does not promise identical
`Generator` streams across releases (NEP 19); with the pinned NumPy 2.5.3 the samples are exact, with another
release they are expected to agree but that is not guaranteed.

| Where | Seeds |
|---|---|
| Phase 2 | 0–49 (main), 0–19 (sensitivity) |
| Phase 3 | 0–49 per cell |
| Phase 4 | 0–11 in every grid; 12–49 added to the 15 headline cells by `--grid headline` |
| Phase 5 inference | the Phase 4 sample A is the run's seed; the R fresh samples B use `100_000 + 100·seed + k` |
| Phase 5 split | fresh samples as in `phase5_split.py` (R = 5 per run) |
| Phase 4 separation and Phase 5 discrete | 20,000 noise-free draws with seed 10,000 and seed 0 |
| Identification diagnostic | the random starts of its refits use the run's seed (Phase 5), 0 (Engel) |
| Phase 6 simulated | 0–19 per law |
| Phase 6 Engel, Phase 7 | PySR `random_state` 0 (Engel) and `1000·seed + k` for restart k (Phase 7) |

**Searches.** PySR runs multithreaded (`parallelism="multithreading"` in `symiv.search.SEARCH_DEFAULTS`; the thread
count is PySR's default `PYTHON_JULIACALL_THREADS=auto`, all logical cores, or the value set for a shard). Phases 2
to 6, except the Engel application, pass no `random_state`. PySR is deterministic only with `deterministic=True`,
`parallelism="serial"` and a fixed `random_state`, which would have multiplied the search time; so **the Pareto fronts
are not bit-reproducible**, with or without the `random_state` that Phases 6 (Engel) and 7 pass. A rerun gives
different candidate formulas and therefore different recovery, coverage and beater rates. The rates are reported with
95% Wilson intervals in every summary; the 15 headline cells have 50 seeds (intervals of ±7 to ±14 points), the other
cells 12 or 20.

**Everything after the search is deterministic.** The run records store every front as SymPy strings (`fronts`),
and every later stage (refits by two-step GMM with seeded starts, selection, metrics, the diagnostic, inference on
fresh samples, the reports) reads those strings. On the original machine the following were verified on 2026-10-02:

- the six report scripts (`phase2_report`, `phase3_report`, `phase4_report` including both figures,
  `phase5_report`, `phase6_simulated --part report`, `phase7_budget --part report`) and `phase5_discrete.py`
  rewrite their committed outputs byte for byte;
- `phase4_analysis.analyze` on saved fronts returns rows identical to the committed `analysis.jsonl` rows;
- `phase6_engel.py --reanalyze` rewrites `engel.json` and `engel.md` identically except the `seconds` field, which
  records wall time;
- `phase5_identification.py --recompute` (630 rows, 19 min with another job running) and `phase6_simulated.py
  --part analyze --recompute` (140 rows, 13 min) rewrite their files with exactly the committed rows; only the row
  order differs, because the workers finish in a different sequence (§5.3 says how to compare).

Across machines, BLAS libraries can change the last digits of refitted constants; the summaries round to one or two
decimals and are expected to match exactly. Data-only statistics, listed in §5.6 as anchors, do not depend on the
search and must match in any replication.

**Phase 3 baselines** also use seeded NumPy and torch generators (`torch.manual_seed(seed)` in `deepiv.py`); with a
fixed seed, torch on CPU repeats a training run on the same machine, while across machines the floating-point
summation order can differ.

---

## 4. Code

### 4.1 The package `src/symiv/`

| Module | Role (README section) |
|---|---|
| `dgp/` | laws and designs D1–D6; `simulate(design, law, n, seed)` returns y, X, Z, the law and the hidden parts (§8.1, §8.2) |
| `criteria/` | spline and polynomial instrument bases, Nyström features, the criterion ‖A′r‖²/n with K ≈ n^{1/3} (§6.2) |
| `gmm.py` | two-step GMM refit with bounded constants and seeded starts; Hansen's J (§6.3) |
| `selection.py` | MMSC and BIC + structure over a candidate set; least-squares selection for plain SR (§6.3) |
| `recovery.py`, `metrics.py` | form recovery, SRBench's SymPy check; function, extrapolation and elasticity errors; implied constants (§8.1) |
| `diagnostics.py` | success / search failure / statistical failure (§7) |
| `identification.py` | first-stage F, AR intervals, the formula confidence set, the verdict (§6.4; THEORY §3.2) |
| `templates.py` | 11 economic shapes with free constants, scored like any candidate (§11, §12.6) |
| `search.py`, `julia/moment_loss.jl` | PySR wrappers; the moment loss evaluated in Julia (§6.6) |
| `baselines/` | fixed forms (oracle and wrong-form IV), sieve 2SLS, KIV, DeepIV, library IV, distillation, control-function SR, SRIT-style (§12.2) |

### 4.2 The scripts `experiments/`

Conventions shared by every script: one JSON line per run, keyed by the run's design, law, n, seed and setting;
a script **skips runs already in its output file**, so an interrupted job resumes and a finished one does nothing
(§5.4 says how to start from scratch); `--shard i --of m` splits a grid over processes; `--limit N` stops after N
runs (for timing); `--workers` sets the analysis processes. Logs of long jobs go to `experiments/phase4/logs/`
(git-ignored).

| Script | Does | Reads | Writes | Flags |
|---|---|---|---|---|
| `fetch_data.py` | downloads the two data files (§2) | the URLs | `data/ak91.dta`, `data/engel95.csv` | `--only ak` or `--only engel`, `--np-version` |
| `smoke_pysr.py` | one end-to-end run, plain PySR against symbolic IV | | stdout | `--design --law --n --seed --niterations --maxsize` |
| `phase2.py` | Phase 2 Monte Carlo on D1 | | `phase2/runs.jsonl` | `--part main` or `--part sensitivity`, `--seeds` |
| `phase2_report.py` | | `phase2/runs.jsonl` | `phase2/summary.md` | |
| `phase3.py` | Phase 3 baselines, 15 methods | | `phase3/runs-{shard}.jsonl` | `--shard --of --deep-threads --limit` |
| `phase3_report.py` | | `phase3/runs-*.jsonl` | `phase3/summary.md` | |
| `phase4.py` | the searches of the full grid; saves every Pareto front | | `phase4/runs-{grid}-{shard}.jsonl` | `--grid breadth nscale nomax cf headline`, `--shard --of --limit --out-dir` |
| `phase4_analysis.py` | selection rules, metrics and diagnostics on the saved fronts; `--separation` computes Theorem 2's margins | `phase4/runs-*.jsonl`, `analysis.jsonl` | `phase4/analysis.jsonl`; `phase4/separation.json` | `--workers`, `--separation` |
| `phase4_report.py` | | `phase4/analysis.jsonl`, `separation.json` | `phase4/summary.md`, `fig_nscale_*.png`, `fig_separation_*.png` | |
| `phase5_inference.py` | inference after selection on fresh samples (Theorem 1 (iii)) | `phase4/runs-breadth-*.jsonl`, `analysis.jsonl` | `phase5/inference.jsonl` | `--workers --limit` |
| `phase5_split.py` | candidates from one sample, selection on another (Corollary 2.3) | `phase4/runs-nscale-*.jsonl` | `phase5/split.jsonl` | `--workers` |
| `phase5_identification.py` | the identification diagnostic on every breadth run (Proposition 5) | `phase4/runs-breadth-*.jsonl`, `runs-headline-0.jsonl`, `analysis.jsonl` | `phase5/identification.jsonl` | `--workers --limit --recompute` |
| `phase5_discrete.py` | a four-constant formula against four moments (Proposition 4) | | `phase5/discrete.md` | |
| `phase5_report.py` | | `phase5/*.jsonl` | `phase5/summary.md` | |
| `phase6_simulated.py` | demand with a cost shifter and labour supply: `--part search`, `analyze`, `report` | `phase6/runs-*.jsonl`, `analysis.jsonl` | `phase6/runs-{shard}.jsonl`, `analysis.jsonl`, `summary.md` | `--part --shard --of --workers --recompute` |
| `phase6_ak.py` | the Angrist–Krueger stress test | `data/ak91.dta` | `phase6/ak.json`, `ak.md` | |
| `phase6_engel.py` | Engel curves, 7 shares × 3 subsamples; `--synthetic` is a self-test on planted data | `data/engel95.csv`, `phase6/engel.json` (with `--reanalyze`) | `phase6/engel.json`, `engel.md`; `engel_synthetic.md` | `--data --shares --subsamples --logexp --instrument --kids --synthetic --reanalyze --out` |
| `phase7_budget.py` | search budget and templates: `--part search`, `analyze`, `report` | Phase 4 and Phase 6 fronts (base arms), `phase7/runs-budget.jsonl` | `phase7/runs-budget.jsonl`, `analysis.jsonl`, `budget.md` | `--part --limit --workers --out-dir --smoke` |

A Phase 4 run record has the keys `grid, design, law, n, seed, setting, params, ops, gens, K, sieve, fronts, times,
errors`; `fronts` maps each generator (`plain`, `onestep`, `distill`, and `cf` in the control-function grid) to its
Pareto front as SymPy strings with complexities and PySR's own pick. The analysis row adds, per selection rule and
candidate set, the selected formula, its refitted constants, recovery, errors and the diagnostic outcome.

---

## 5. Instructions

### 5.1 Install

From the repository root, with Python 3.12 on the path:

```
python -m venv .venv
.venv\Scripts\activate                     # Windows; elsewhere: source .venv/bin/activate
pip install -r replication/requirements-frozen.txt     # the exact environment of the reported runs
python -c "import pysr"                    # installs Julia 1.11 and SymbolicRegression.jl into .venv/julia_env (several minutes, needs network)
```

`pip install -e ".[search,dev,apps,deep]"` installs the newest versions within the bounds of `pyproject.toml`
instead of the frozen set. The `deep` extra (torch) is needed only for the DeepIV baseline of Phase 3; install the CPU
build with `--index-url https://download.pytorch.org/whl/cpu`.

### 5.2 Verify the installation

```
pytest                                     # expected: 94 passed, 3 deselected, in about 20 s
pytest -m julia                            # the two PySR tests, about a minute (the Julia loss equals the Python criterion; the front is SymPy)
python experiments/smoke_pysr.py --design D1 --law power --n 2000     # about 6 minutes
```

The smoke test prints, for one D1 sample with the law 2x^0.7: plain PySR's own pick with its recovery flag and its
error ‖f̂ − f₀‖/sd(f₀); the symbolic-IV Pareto front scored by MMSC, best first, with J and the number of
constants p; the selected formula, its error and the outcome ("success" when the selection has the true form). The
formulas differ from run to run (§3.4). What should hold: the selection has the power form with constants near 2 and
0.7 and an error of a few hundredths of a sd, while plain PySR's pick, whether or not it has the power form, sits
farther from f₀ because it fits the conditional mean (0.093 against 0.014 in the run recorded for this guide).

### 5.3 Check A: recompute everything from the saved searches

Because the scripts skip finished work, recomputing means either using a `--recompute` flag or removing the output
file first (the committed copy stays in git). The data file is needed for the Engel step only.

```
python experiments/phase2_report.py
python experiments/phase3_report.py
del experiments\phase4\analysis.jsonl             # rm on POSIX
python experiments/phase4_analysis.py --workers 8                 # about 2 h 20 min
python experiments/phase4_analysis.py --separation --workers 8    # about 25 min
python experiments/phase4_report.py
del experiments\phase5\inference.jsonl experiments\phase5\split.jsonl
python experiments/phase5_inference.py --workers 8
python experiments/phase5_split.py --workers 8
python experiments/phase5_identification.py --workers 8 --recompute   # 15 min
python experiments/phase5_discrete.py
python experiments/phase5_report.py
python experiments/phase6_simulated.py --part analyze --workers 8 --recompute   # 12 min
python experiments/phase6_simulated.py --part report
python experiments/fetch_data.py --only engel
python experiments/phase6_engel.py --data data/engel95.csv --reanalyze          # 3 min
del experiments\phase7\analysis.jsonl
python experiments/phase7_budget.py --part analyze --workers 8    # about 1 h 30 min
python experiments/phase7_budget.py --part report
```

Expected outcome: `git status` shows no change, with these exceptions: the `seconds` fields of `engel.json` and the
"N s" at the end of the detail lines in `engel.md`; and the **row order** of the JSONL files written by several
workers (`identification.jsonl` and the `analysis.jsonl` files), which differs from run to run while the rows are the
same. To compare ignoring order:

```
python -c "import json,subprocess as s;f='experiments/phase5/identification.jsonl';a=sorted(s.run(['git','show','HEAD:'+f],capture_output=True,text=True,encoding='utf-8').stdout.splitlines());b=sorted(open(f,encoding='utf-8').read().splitlines());print('identical rows' if a==b else 'DIFFERENT')"
```

(replace the path for the other files). The reports read the rows in any order and are unchanged.

### 5.4 Check B: rerun from scratch

1. Move the committed results aside (or delete them; `git checkout -- experiments` restores them at any time):

   ```
   python replication/clear_results.py                       # lists the 38 files
   python replication/clear_results.py --move-to replication/reference    # or --yes to delete
   ```

2. Fetch the data: `python experiments/fetch_data.py` (§2).

3. Run the chain. `replication\run_all.cmd` (Windows) or `bash replication/run_all.sh` runs every step of §4.2 in
   order with one process per step, about 40 hours, writing logs to `experiments/phase4/logs/`. Each step is the
   command that produced the committed results; the chain as a whole was assembled for this guide and was not run
   end to end in one invocation. On Windows a job that must outlive the terminal is started detached:

   ```
   powershell -Command "Start-Process cmd.exe -ArgumentList '/c','replication\run_all.cmd' -WindowStyle Hidden"
   ```

   On POSIX: `nohup bash replication/run_all.sh &`. To halve the wall time, run Phases 3 and 4 as two shards in two
   terminals, each with `PYTHON_JULIACALL_THREADS=4`:

   ```
   python experiments/phase3.py --shard 0 --of 2        # and --shard 1 --of 2
   python experiments/phase4.py --grid breadth nscale nomax cf --shard 0 --of 2     # and --shard 1 --of 2
   ```

   then continue with `phase3_report.py`, `phase4.py --grid headline` and the rest of the chain. Any interrupted
   step is resumed by running the same command again.

4. Compare with the committed results: `git diff --stat`, then `git diff experiments/phase4/summary.md` and the
   other summaries. §5.6 says what to expect.

### 5.5 Partial reruns

- The Phase 2 Monte Carlo with 5 seeds per cell (20 runs, about 15 minutes): `python experiments/phase2.py --part
  main --seeds 5` after moving `experiments/phase2/runs.jsonl` aside, then `phase2_report.py`.
- The identification diagnostic alone: `phase5_identification.py --recompute` (15 min; only the Phase 4 fronts and
  analysis are needed).
- A search grid into a separate directory, leaving the committed records untouched: `phase4.py --grid nomax --out-dir
  some/dir`.
- The budget experiment on a tiny budget, to test the pipeline: `phase7_budget.py --part search --smoke --out-dir
  some/dir`, then `--part analyze` and `--part report` with the same `--out-dir`.

### 5.6 What to expect from Check B

**Must match exactly** (they depend on the data, not on the search): the oracle and wrong-form IV rows of Phase 3;
the first-stage F statistics of every cell and of the applications (Engel: F = 31 to 59; Angrist–Krueger: 4.9 with
30 instruments and 34 with 3); the Angrist–Krueger OLS and 2SLS returns (0.071 and 0.089 with 30 instruments; 0.103
with 3); the sieve-2SLS J statistics; the S tests of the fixed Working–Leser and quadratic Engel forms and the AR
interval of the quadratic term; the separation margins of `separation.json` for formulas that appear again; the
discrete-instrument table.

**Match in distribution**: every recovery, coverage and beater rate, the selected formulas and their errors, the
identification verdict shares. Each summary prints a 95% Wilson interval next to each rate; a replication should fall
inside them in about 19 cases out of 20. The headline cells (README §12.3, 50 seeds) have intervals of ±7 to ±14
points; 12-seed cells are wider. The qualitative findings of README §12 (D1 and D3 recover the laws while D5 does not;
the structure term's gain; recovery rising with n; the Engel and labour-supply shapes; what the budget experiment
shows) do not hinge on any single cell.

**Known to be fragile**: cells reported at 0% or 100% with 12 seeds can show one success or failure; the selected
formula in an application can change among near-duplicates (README §12.5 reports the picks together with the
confidence set for that reason).

---

## 6. Tables and figures: where each one comes from

README §12 quotes the summaries; the summaries are written from the run records; the records are written by the
search and analysis scripts. Section numbers refer to the Markdown files.

| Reported in | Produced by | From | Source records |
|---|---|---|---|
| README §12.1, table "Law, setting …" and the text | `phase2_report.py` → `phase2/summary.md` (per-cell sections, "Symbolic IV outcomes", "Sensitivity to K and C") | | `phase2/runs.jsonl` ← `phase2.py` |
| README §12.2, table "Cell, f₀, Symbolic IV, …" | `phase3_report.py` → `phase3/summary.md` ("Headline" and per-cell sections) | | `phase3/runs-0.jsonl`, `runs-1.jsonl` ← `phase3.py` |
| README §12.3, breadth table "Law, D1 … D5" | `phase4_report.py` → `phase4/summary.md` §1 | `phase4/analysis.jsonl` ← `phase4_analysis.py` | `phase4/runs-breadth-*.jsonl`, `runs-headline-0.jsonl` ← `phase4.py` |
| README §12.3, table "Rule × candidate set" and the coverage/beaters text | `phase4/summary.md` §2 and §3 | same | same |
| README §12.3, figure `fig_nscale` | `phase4_report.py` → `phase4/summary.md` §4 and `fig_nscale_{light,dark}.png` | same | `runs-nscale-*.jsonl`, the n-scaling cells of `runs-headline-0.jsonl` |
| README §12.3, operator ablation and control-function paragraphs | `phase4/summary.md` §5 and §6 | same | `runs-nomax-*.jsonl`, `runs-cf-*.jsonl` |
| README §12.3, figure `fig_separation`; THEORY §7 table and §7.1 | `phase4_report.py` → `phase4/summary.md` §7 and `fig_separation_{light,dark}.png` | `phase4/separation.json` ← `phase4_analysis.py --separation` | `phase4/analysis.jsonl` |
| README §12.4, table "Constants covered, f(median), elasticity, J rejects, AR covers"; THEORY §7.1 | `phase5_report.py` → `phase5/summary.md` §1 | `phase5/inference.jsonl` ← `phase5_inference.py` | Phase 4 breadth fronts and analysis |
| README §12.4 and THEORY §7.1, split-sample selection (Corollary 2.3) | `phase5/summary.md` §2 | `phase5/split.jsonl` ← `phase5_split.py` | Phase 4 n-scaling fronts |
| README §12.4, table "Runs, flagged, true form in the confidence set"; THEORY §3.2 (Proposition 5(b) count) and §7.1 | `phase5/summary.md` §3 | `phase5/identification.jsonl` ← `phase5_identification.py` | Phase 4 breadth and headline fronts and analysis |
| THEORY §5, "Checked in the data" | `phase5_discrete.py` → `phase5/discrete.md` | | simulated, seed 0 |
| README §12.5, table "Environment, Law, …" and the four bullets | `phase6_simulated.py --part report` → `phase6/summary.md` | `phase6/analysis.jsonl` ← `--part analyze` | `phase6/runs-0.jsonl` ← `--part search` |
| README §12.5, Engel table and bullets | `phase6_engel.py` → `phase6/engel.md`, `engel.json`; the planted-share sentence ← `--synthetic` → `engel_synthetic.md` | | `data/engel95.csv` |
| README §12.5, Angrist–Krueger bullets | `phase6_ak.py` → `phase6/ak.md`, `ak.json` | | `data/ak91.dta` |
| README §12.6, table "Cell, Law, Base, Base + templates, Large, Large + templates" and the findings; THEORY §7 table (last row) | `phase7_budget.py --part report` → `phase7/budget.md` §1–4 | `phase7/analysis.jsonl` ← `--part analyze` | `phase7/runs-budget.jsonl` ← `--part search`; Phase 4 and 6 fronts for the base arms |
| README §11 and §12 headline sentences ("98–100% from n = 5000", "0–2% over 50 seeds", "630 runs", …) | the same summaries | | |

---

## 7. Inventory of the committed results

Record counts are lines of the JSONL files. `replication/checksums.sha256` has the SHA-256 of each file;
`sha256sum -c replication/checksums.sha256` (or `Get-FileHash` on Windows) checks a copy of the repository.

| File | Records | Notes |
|---|---|---|
| `phase2/runs.jsonl` | 285 lines = 280 runs + 5 superseded error records | the first attempt at 5 runs failed inside a refit ("array must not contain infs or NaNs"); the resume redid them, and the report uses the 280 good rows |
| `phase2/summary.md` | | |
| `phase3/runs-0.jsonl`, `runs-1.jsonl` | 150 + 150 | two shards |
| `phase3/summary.md` | | |
| `phase4/runs-breadth-0.jsonl`, `-1`, `-2` | 142 + 143 + 3 = 288 | the three runs of `-2` (D1, log law, seeds 2, 5, 8) were completed by a separate invocation; the analysis reads every `runs-*.jsonl` and the 288 keys are distinct |
| `phase4/runs-nscale-0.jsonl`, `-1` | 72 + 72 | |
| `phase4/runs-nomax-0.jsonl`, `-1` | 24 + 24 | |
| `phase4/runs-cf-0.jsonl`, `-1` | 24 + 24 | |
| `phase4/runs-headline-0.jsonl` | 570 | seeds 12–49 of the 15 headline cells |
| `phase4/analysis.jsonl` | 1,098 | one row per search run |
| `phase4/separation.json` | 523 lines | one entry per cell, with the closest wrong formula and the margin at each n |
| `phase4/summary.md`, `fig_nscale_light.png`, `fig_nscale_dark.png`, `fig_separation_light.png`, `fig_separation_dark.png` | | |
| `phase5/inference.jsonl` | 4,500 | per (run, tree, sample) |
| `phase5/split.jsonl` | 672 | |
| `phase5/identification.jsonl` | 630 | one per breadth run (288 + 342 headline additions) |
| `phase5/discrete.md`, `phase5/summary.md` | | |
| `phase6/runs-0.jsonl`, `analysis.jsonl` | 140 + 140 | 7 laws × 20 seeds |
| `phase6/summary.md`, `ak.json`, `ak.md`, `engel.json`, `engel.md`, `engel_synthetic.md` | | |
| `phase7/runs-budget.jsonl`, `analysis.jsonl` | 88 + 352 | 88 runs × 4 arms |
| `phase7/budget.md` | | |

Not in the package: `data/` (§2), `experiments/phase4/logs/` (job logs; the timings of §3.3 come from them),
`outputs/` (PySR's hall-of-fame files, which it writes during a search; safe to delete).

---

## 8. Known issues and troubleshooting

- **Julia install fails with `GitError … could not find repository at …\.julia\registries\General`.** The user-wide
  Julia registry is corrupt. Move that folder outside `registries/` (Julia reads every folder inside it) and rerun
  `python -c "import pysr"`; a fresh registry is downloaded.
- **`pysr` cannot be imported.** Check that the virtual environment's interpreter is the one running
  (`.venv\Scripts\python.exe`); a system Python without the `search` extra fails at `import pysr`.
- **pytest shows no Julia crash traces.** `pyproject.toml` disables pytest's faulthandler on purpose: Julia raises
  access violations at garbage-collection safepoints, which the faulthandler would print as crashes.
- **Long jobs and closed terminals.** A search grid runs for hours. On Windows start it detached (§5.4); on POSIX use
  `nohup`. Every script resumes where it stopped.
- **A step does nothing.** Its output file already holds every run (§4.2). Use `--recompute` where it exists, or move
  the file aside, or `replication/clear_results.py`.
- **Row order.** Analysis files written by several workers list rows in completion order; compare them sorted (§5.3).
- **The np tarball URL returns 404.** A newer np has reached CRAN and 0.70-5 moved to the archive; `fetch_data.py`
  tries the archive URL automatically. If the archive copy is also gone, pass `--np-version` with the current version.
- **The Mastering 'Metrics URL has moved.** Download `ak91.dta` from the book's data page and place it in `data/`;
  the checksum in §2 confirms it is the same file.
- **NumPy other than 2.5.3.** Simulated samples may differ in the last bits if NumPy changed a `Generator` method;
  the recovery rates are unaffected in distribution, and the deterministic anchors of §5.6 move only in their last
  digits.
- **Timestamps** in the logs and in this guide are local time (UTC+1).

---

## 9. Licence, citation and contact

The code, scripts and run records are the work of Manuel Sanchez and are released under the MIT licence
(`LICENSE`); the working paper in `paper/` is under CC BY 4.0 (`paper/LICENSE.md`); the third-party data are not
redistributed and remain under their sources' terms (§2). Cite the paper and this repository's commit hash
(`git rev-parse HEAD`), or the Zenodo DOI of the release, when reporting a replication; `CITATION.cff` has the
citation. For double-blind review, remove this section from the submitted copy.
