"""Tables and figures for Phase 4 -> experiments/phase4/summary.md and phase4/fig_*_{light,dark}.png.

Reads phase4/analysis.jsonl and phase4/separation.json (from phase4_analysis.py), plus
Phase 3 runs for the control-function baseline at gamma = 0.3.
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.stats import binomtest, spearmanr

from phase2_report import med, wilson

HERE = Path(__file__).parent
OUT = HERE / "phase4"
LAWS = {"log": "1 + 2 log x", "power": "2 x^0.7", "kink": "x - 0.8 max(x - 1.5, 0)", "saturation": "3x / (1 + x)",
        "cobb_douglas": "1.5 x1^0.3 x2^0.5"}
DESIGNS = {"D1": "confounding", "D2": "heterosk. first stage", "D3": "simultaneity", "D4": "discrete Z (J = 4)", "D5": "weak Z (π = 0.1)"}
SETS = ["plain", "onestep", "distill", "library", "iv", "pooled"]
SET_LABEL = {"plain": "Plain PySR front", "onestep": "One-step IV front", "distill": "Distilled sieve front",
             "library": "Library Lasso path", "iv": "One-step + distilled", "pooled": "All pooled"}
RULES = ["bic", "hqic", "aic", "bic_s05", "bic_s1", "bic_K2", "bic_mmr", "cv"]
RULE_LABEL = {"bic": "MMSC-BIC", "hqic": "MMSC-HQIC", "aic": "MMSC-AIC", "bic_s05": "BIC + structure (w = 0.5)",
              "bic_s1": "BIC + structure (w = 1)", "bic_K2": "BIC, 2K instruments", "bic_mmr": "BIC, kernel instruments",
              "cv": "Cross-fitted criterion"}


def load():
    runs = [json.loads(line) for line in (OUT / "analysis.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in runs if "error" in r]
    runs = [r for r in runs if "error" not in r]
    sep_file = OUT / "separation.json"
    sep = {s["cell"]: s for s in json.loads(sep_file.read_text())} if sep_file.exists() else {}
    return runs, errors, sep


def cell_key(r):
    return json.dumps([r["design"], r["law"], r["params"]], sort_keys=True)


def rate(xs) -> str:
    xs = list(xs)
    return wilson(sum(xs), len(xs)) if xs else "–"


def pct(xs) -> str:
    xs = list(xs)
    return f"{100 * np.mean(xs):.0f}%" if xs else "–"


def mcnemar(a: list[bool], b: list[bool]) -> str:
    """Runs recovered only by a / only by b, and the exact two-sided p."""
    only_a = sum(x and not y for x, y in zip(a, b))
    only_b = sum(y and not x for x, y in zip(a, b))
    p = binomtest(only_a, only_a + only_b).pvalue if only_a + only_b else 1.0
    return f"+{only_a} / −{only_b} (p = {p:.3f})"


def sel(r, s, rule="bic"):
    return r["select"].get(s, {}).get(rule)


# ------------------------------------------------------------------ figures

THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781", grid="#e1e0d9",
                  series=["#2a78d6", "#eb6834", "#1baf7a", "#eda100"]),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781", grid="#2c2c2a",
                 series=["#3987e5", "#d95926", "#199e70", "#c98500"]),
}


def _axes_style(ax, t):
    ax.set_facecolor(t["surface"])
    ax.grid(True, color=t["grid"], linewidth=1, linestyle="-")
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(t["grid"])
    ax.tick_params(colors=t["muted"], labelcolor=t["ink2"], labelsize=9)


def _end_labels(ax, ends, t, min_gap=7.0):
    """Direct labels at line ends, in ink; skipped where they would collide (the legend still names them)."""
    placed = []
    for y, x, text in sorted(ends, key=lambda e: -e[0]):
        if all(abs(y - py) >= min_gap for py in placed):
            ax.annotate(text, (x, y), xytext=(6, 0), textcoords="offset points", va="center", fontsize=8.5, color=t["ink2"])
            placed.append(y)


def figure_nscale(table: dict, theme: str) -> Path:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.ticker

    t = THEMES[theme]
    series = [("distill", "Distilled sieve + MMSC"), ("plain", "Plain PySR front + MMSC"),
              ("onestep", "One-step IV + MMSC"), ("plain_pick", "Plain PySR (its own pick)")]
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.8), sharey=True, facecolor=t["surface"])
    for ax, law in zip(axes, ("power", "log")):
        _axes_style(ax, t)
        ends = []
        for i, ((key, label), color) in enumerate(zip(series, t["series"])):
            pts = sorted((n, v) for (lw, n, k), v in table.items() if lw == law and k == key)
            if not pts:
                continue
            xs, ys = zip(*pts)
            dodge = 1.07 ** (i - 1.5)  # small horizontal offset so tied points stay visible
            ax.plot([x * dodge for x in xs], ys, color=color, linewidth=2, solid_joinstyle="round", solid_capstyle="round",
                    label=label, marker="o", markersize=8, markerfacecolor=color, markeredgecolor=t["surface"],
                    markeredgewidth=2)
            # Direct label only where no other series ends up close by; the legend carries identity otherwise.
            others = [v for (lw, n, k), v in table.items() if lw == law and k != key and n == xs[-1]]
            if all(abs(v - ys[-1]) > 8 for v in others):
                ends.append((ys[-1], xs[-1] * dodge, label.split(" (")[0].replace(" + MMSC", "")))
        _end_labels(ax, ends, t)
        ax.set_xscale("log")
        ax.xaxis.set_minor_locator(matplotlib.ticker.NullLocator())
        ax.set_xlim(800, 140_000)
        ax.set_ylim(-4, 104)
        ax.set_xticks([1000, 2000, 5000, 10000, 20000, 50000])
        ax.set_xticklabels(["1k", "2k", "5k", "10k", "20k", "50k"])
        ax.set_title(f"f₀ = {LAWS[law]}", color=t["ink"], fontsize=10.5, loc="left")
        ax.set_xlabel("Sample size n", color=t["ink2"], fontsize=9.5)
    axes[0].set_ylabel("True form recovered (%)", color=t["ink2"], fontsize=9.5)
    leg = fig.legend(*axes[0].get_legend_handles_labels(), loc="upper center", ncol=4, frameon=False, fontsize=9,
                     bbox_to_anchor=(0.5, 1.02))
    for txt in leg.get_texts():
        txt.set_color(t["ink2"])
    fig.suptitle("Recovery as n grows (D1 strong: π = 0.7, ρ = 1.2; MMSC with structure term; 12 seeds per point)",
                 color=t["ink"], fontsize=11, y=1.1, x=0.06, ha="left")
    fig.tight_layout()
    path = OUT / f"fig_nscale_{theme}.png"
    fig.savefig(path, dpi=150, bbox_inches="tight", facecolor=t["surface"])
    plt.close(fig)
    return path


def figure_separation(points: list[tuple], theme: str) -> Path:
    """Recovery given coverage against the population margin; points are (group, margin, recovery %)."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    t = THEMES[theme]
    fig, ax = plt.subplots(figsize=(7.5, 4), facecolor=t["surface"])
    _axes_style(ax, t)
    ax.axvline(0, color=t["muted"], linewidth=1, linestyle=(0, (4, 3)), zorder=1)
    above = matplotlib.transforms.blended_transform_factory(ax.transData, ax.transAxes)
    for text, dx, ha in (("← wrong formula wins", -6, "right"), ("truth wins →", 6, "left")):
        ax.annotate(text, (0, 1.0), xycoords=above, xytext=(dx, 4), textcoords="offset points", ha=ha, va="bottom",
                    fontsize=8.5, color=t["ink2"])
    for (group, label), color in zip((("breadth", "Breadth grid cells (n = 2000)"), ("nscale", "n-scaling points (D1 strong)")),
                                     t["series"]):
        pts = [(m, rec) for g, m, rec in points if g == group]
        if pts:
            xs, ys = zip(*pts)
            ax.scatter(xs, ys, s=64, color=color, edgecolors=t["surface"], linewidths=2, label=label, zorder=3)
    ax.set_xscale("symlog", linthresh=10)
    ticks = [-10, 0, 10, 100, 1000, 10000]
    ax.set_xticks(ticks)
    ax.set_xticklabels(["−10", "0", "10", "100", "1,000", "10,000"])
    ax.xaxis.set_minor_locator(matplotlib.ticker.NullLocator())
    ax.set_ylim(-4, 104)
    ax.set_xlabel("Population margin of the closest wrong formula with ≤ p₀ constants:  n·δ̂/σᵤ² − (p₀ − p)·ln n",
                  color=t["ink2"], fontsize=9.5)
    ax.set_ylabel("Recovery given coverage (%)", color=t["ink2"], fontsize=9.5)
    ax.set_title("Recovery against Theorem 2's margin (all candidates + MMSC-BIC)", color=t["ink"], fontsize=10.5, loc="left",
                 pad=22)
    leg = ax.legend(frameon=False, fontsize=9, loc="center right")
    for txt in leg.get_texts():
        txt.set_color(t["ink2"])
    fig.tight_layout()
    path = OUT / f"fig_separation_{theme}.png"
    fig.savefig(path, dpi=150, bbox_inches="tight", facecolor=t["surface"])
    plt.close(fig)
    return path


# ------------------------------------------------------------------ report


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    runs, errors, sep = load()
    L = []
    w = L.append
    by_grid = defaultdict(list)
    for r in runs:
        by_grid[r["grid"]].append(r)
    w("# Phase 4 results\n")
    w(f"Generated by `experiments/phase4_report.py` from {len(runs)} analysed runs ({len(errors)} analysis errors): "
      + ", ".join(f"{g} {len(v)}" for g, v in by_grid.items()) + ". 12 seeds per cell. Recovery = the selected formula has "
      "the true form (§8.1); rates show 95% Wilson intervals. Errors are RMS(f̂ − f₀) in units of the in-sample sd of f₀. "
      "Paired comparisons (+a / −b) count runs recovered only by the row's method / only by the reference, with exact McNemar p.\n")

    # ---- 1. breadth map
    B = by_grid.get("breadth", [])
    if B:
        w("## 1. Breadth: five laws × five designs (n = 2000)\n")
        w("| Design | Law | Plain PySR, own pick | One-step + MMSC | Distilled + MMSC | Library path + MMSC | **All pooled + MMSC** | "
          "Any candidate has the true form | Pooled: in-sample error | Pooled: extrapolation error | Sieve curve error |")
        w("|---|---|---|---|---|---|---|---|---|---|---|")
        for design in DESIGNS:
            for law in LAWS:
                rs = [r for r in B if r["design"] == design and r["law"] == law]
                if not rs:
                    continue
                cells = [pct(r["pysr_pick"]["plain"]["recovered"] for r in rs if "plain" in r["pysr_pick"])]
                for s in ("onestep", "distill", "library", "pooled"):
                    v = [sel(r, s)["recovered"] for r in rs if sel(r, s)]
                    cells.append(pct(v) if s != "pooled" else f"**{pct(v)}**")
                cells.append(pct(r["coverage"]["pooled"] for r in rs))
                cells += [med(sel(r, "pooled")["rel_error"] for r in rs), med(sel(r, "pooled")["extrap_error"] for r in rs),
                          med(r["sieve"]["rel_error"] for r in rs if r.get("sieve"))]
                w(f"| {design} {DESIGNS[design]} | {LAWS[law]} | " + " | ".join(cells) + " |")
        w("")

    # ---- 2. selection rules
    pool_runs = [r for r in runs if r["grid"] in ("breadth", "nomax", "cf") or (r["grid"] == "nscale" and r["n"] <= 5000)]
    pool_runs = [r for r in pool_runs if "cv" in r["select"].get("pooled", {})]
    if pool_runs:
        w("## 2. Selection rules × candidate sets\n")
        w(f"All runs with n ≤ 5000 ({len(pool_runs)}). Recovery rate; in the last column, the pooled set's paired comparison against MMSC-BIC.\n")
        sets_present = [s for s in SETS if any(s in r["select"] for r in pool_runs)]
        w("| Rule | " + " | ".join(SET_LABEL[s] for s in sets_present) + " | All pooled vs. MMSC-BIC |")
        w("|---|" + "---|" * (len(sets_present) + 1))
        for rule in RULES:
            row = [pct(sel(r, s, rule)["recovered"] for r in pool_runs if sel(r, s, rule)) for s in sets_present]
            a = [sel(r, "pooled", rule)["recovered"] for r in pool_runs]
            b = [sel(r, "pooled", "bic")["recovered"] for r in pool_runs]
            w(f"| {RULE_LABEL[rule]} | " + " | ".join(row) + f" | {'–' if rule == 'bic' else mcnemar(a, b)} |")
        w("\nMedian in-sample error of the pooled set's choice: "
          + "; ".join(f"{RULE_LABEL[rule]} {med(sel(r, 'pooled', rule)['rel_error'] for r in pool_runs)}" for rule in RULES) + ".\n")

    # ---- 3. mechanism
    mech = [r for r in runs if r["grid"] in ("breadth", "nscale", "nomax", "cf")]
    if mech:
        w("## 3. Why candidate sets differ: coverage and beaters\n")
        w("Coverage: the set contains a formula with the true form. Beaters: wrong formulas (cannot represent f₀) whose "
          "MMSC-BIC beats the true form's. Recovery given coverage separates candidate generation from selection.\n")
        w("| Candidate set | Runs | Candidates, median | Coverage | Beaters, mean | Runs with ≥ 1 beater | Recovery (BIC) | Recovery given coverage |")
        w("|---|---|---|---|---|---|---|---|")
        for s in SETS:
            rs = [r for r in mech if s in r["coverage"]]
            if not rs:
                continue
            cov = [r["coverage"][s] for r in rs]
            recs = [sel(r, s)["recovered"] for r in rs]
            given = [x for x, c in zip(recs, cov) if c]
            w(f"| {SET_LABEL[s]} | {len(rs)} | {np.median([r['n_candidates'][s] for r in rs]):.0f} | {pct(cov)} | "
              f"{np.mean([r['beaters'][s] for r in rs]):.2f} | {pct(r['beaters'][s] > 0 for r in rs)} | {pct(recs)} | {pct(given)} |")
        w("")

    # ---- 4. n-scaling
    N = by_grid.get("nscale", [])
    nscale_table = {}
    if N:
        w("## 4. Recovery as n grows (D1 strong: π = 0.7, ρ = 1.2)\n")
        w("Each MMSC cell is recovery under MMSC-BIC / under BIC + structure (w = 0.5), of 12 seeds. The plain front is "
          "PySR's squared-error search scored by the IV criterion instead of by its own pick.\n")
        w("| Law | n | Plain PySR, own pick | Plain front + MMSC | One-step + MMSC | Distilled + MMSC | All pooled + MMSC | "
          "Plain front: coverage | Distilled: coverage | Pooled (structure): in-sample error | Sieve curve error |")
        w("|---|---|---|---|---|---|---|---|---|---|---|")
        for law in ("power", "log"):
            for n in sorted({r["n"] for r in N}):
                rs = [r for r in N if r["law"] == law and r["n"] == n]
                if not rs:
                    continue
                cells = []
                for k in ("plain", "onestep", "distill", "pooled"):
                    v = {rule: [sel(r, k, rule)["recovered"] for r in rs if sel(r, k, rule)] for rule in ("bic", "bic_s05")}
                    if v["bic_s05"]:
                        nscale_table[(law, n, k)] = 100 * np.mean(v["bic_s05"])
                    cells.append(f"{pct(v['bic'])} / {pct(v['bic_s05'])}" if v["bic"] else "–")
                pp = [r["pysr_pick"]["plain"]["recovered"] for r in rs if "plain" in r["pysr_pick"]]
                if pp:
                    nscale_table[(law, n, "plain_pick")] = 100 * np.mean(pp)
                w(f"| {LAWS[law]} | {n} | {pct(pp)} | " + " | ".join(cells) + " | "
                  f"{pct(r['coverage']['plain'] for r in rs if 'plain' in r['coverage'])} | {pct(r['coverage']['distill'] for r in rs)} | "
                  f"{med(sel(r, 'pooled', 'bic_s05')['rel_error'] for r in rs)} | {med(r['sieve']['rel_error'] for r in rs if r.get('sieve'))} |")
        w("")
        if nscale_table:
            for theme in THEMES:
                figure_nscale(nscale_table, theme)
            w('<picture><source media="(prefers-color-scheme: dark)" srcset="fig_nscale_dark.png">'
              '<img alt="Recovery rate against sample size for each candidate generator scored by MMSC with the structure term, and for plain PySR’s own pick; the same numbers are in the table above." '
              'src="fig_nscale_light.png"></picture>\n')

    # ---- 5. operator ablation (paired on the same data)
    NM = by_grid.get("nomax", [])
    if NM:
        w("## 5. Operator ablation: without `max` (paired on the same data)\n")
        w("Reference runs with `max`: the breadth grid (D1 default) and n-scaling at n = 2000 (D1 strong), same seeds.\n")
        w("| Setting | Law | Set | With `max` | Without `max` | Without vs. with |")
        w("|---|---|---|---|---|---|")
        ref = {}
        for r in runs:
            if (r["grid"] == "breadth" and r["design"] == "D1") or (r["grid"] == "nscale" and r["n"] == 2000):
                ref[(r["setting"], r["law"], r["seed"])] = r
        for setting in ("default", "strong"):
            for law in ("power", "log"):
                pairs = [(ref[(setting, law, r["seed"])], r) for r in NM
                         if r["setting"] == setting and r["law"] == law and (setting, law, r["seed"]) in ref]
                for s in ("onestep", "distill", "iv"):
                    a = [sel(nm, s)["recovered"] for _, nm in pairs if sel(nm, s)]
                    b = [sel(wm, s)["recovered"] for wm, _ in pairs if sel(wm, s)]
                    if a and len(a) == len(b):
                        w(f"| {setting} | {LAWS[law]} | {SET_LABEL[s]} | {pct(b)} | {pct(a)} | {mcnemar(a, b)} |")
        w("")

    # ---- 6. control function
    C = by_grid.get("cf", [])
    if C:
        w("## 6. Control-function SR when its assumption fails more (D2)\n")
        w("| γ | Law | Seeds | Control-function SR: recovered | CF: in-sample error | Distilled + MMSC: recovered | Distilled: in-sample error |")
        w("|---|---|---|---|---|---|---|")
        p3 = []
        for f in sorted((HERE / "phase3").glob("runs-*.jsonl")):
            p3 += [json.loads(line) for line in f.read_text().splitlines() if line.strip()]
        for law in ("power", "log"):
            rs = [r for r in p3 if r["design"] == "D2" and r["law"] == law]
            if rs:
                m = [r["methods"] for r in rs]
                w(f"| 0.3 (Phase 3) | {LAWS[law]} | {len(rs)} | {pct(x['control_function_sr']['recovered'] for x in m)} | "
                  f"{med(x['control_function_sr']['rel_error'] for x in m)} | {pct(x['distill_sieve_iv_mmsc']['recovered'] for x in m)} | "
                  f"{med(x['distill_sieve_iv_mmsc']['rel_error'] for x in m)} |")
        for gamma in sorted({r["params"]["gamma"] for r in C}):
            for law in ("power", "log"):
                rs = [r for r in C if r["params"]["gamma"] == gamma and r["law"] == law]
                if rs:
                    w(f"| {gamma} | {LAWS[law]} | {len(rs)} | {pct(r['cf']['recovered'] for r in rs)} | {med(r['cf']['rel_error'] for r in rs)} | "
                      f"{pct(sel(r, 'distill')['recovered'] for r in rs)} | {med(sel(r, 'distill')['rel_error'] for r in rs)} |")
        w("")

    # ---- 7. separation
    if sep:
        w("## 7. Separation and Theorem 2\n")
        w("A wrong formula with p ≤ p₀ constants beats the truth under MMSC-BIC when its J statistic is below the penalty it "
          "saves, (p₀ − p)·ln n. In the population its J is about λ = n·δ̂/σᵤ², where δ̂ = min_θ ‖P_A(f_θ − f₀)‖²/n is computed "
          "on 20,000 noise-free draws with the instruments the selection used at that n (K ≈ n^(1/3); polynomial degree 4 for "
          "two regressors). The **margin** is the smallest λ − (p₀ − p)·ln n over the wrong formulas with p ≤ p₀ that any "
          "search produced in the cell; positive means the closest such formula loses in the population. Wrong formulas with "
          "more constants than f₀ can win only by fitting noise (the contrived winners; §3 counts them as beaters), so they "
          "are not in the margin. Separation explains selection, not search, so recovery is shown among runs whose pooled "
          "candidates contain the true form.\n")
        w("| Grid | Design | Law | n | Wrong formulas with p ≤ p₀ | Closest wrong formula (p) | δ̂ / var(f₀) | λ | Margin | "
          "Coverage | Recovery given coverage | Recovery |")
        w("|---|---|---|---|---|---|---|---|---|---|---|---|")
        points = []
        groups = defaultdict(list)
        for r in runs:
            if r["grid"] in ("breadth", "nscale") and cell_key(r) in sep:
                groups[(r["grid"], cell_key(r), r["n"])].append(r)
        for (grid, ck, n), rs in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])):
            sp_ = sep[ck]
            best = sp_["by_n"].get(str(n))
            rec_cov = [sel(r, "pooled")["recovered"] for r in rs if r["coverage"]["pooled"]]
            recs = [sel(r, "pooled")["recovered"] for r in rs]
            design, law, _ = json.loads(ck)
            if best is None:
                cells = "none observed | – | – | – "
            else:
                closest = best["closest"][:48].replace("|", "\\|")
                cells = f"`{closest}` ({best['p']}) | {best['delta_rel']:.1e} | {best['lam']:.0f} | {best['margin']:.0f} "
                if rec_cov:
                    points.append((grid, best["margin"], 100 * np.mean(rec_cov)))
            w(f"| {grid} | {design} | {LAWS[law]} | {n} | {sp_['n_forms']} | {cells}| {pct(r['coverage']['pooled'] for r in rs)} | "
              f"{pct(rec_cov)} | {pct(recs)} |")
        if len(points) > 3:
            ms, ys = [x[1] for x in points], [x[2] for x in points]
            rho, p = spearmanr(ms, ys)
            pos = [y for m, y in zip(ms, ys) if m > 0]
            neg = [y for m, y in zip(ms, ys) if m <= 0]
            w(f"\nAcross the {len(points)} cells with such a wrong formula and at least one covered run: Spearman correlation "
              f"between the margin and recovery given coverage {rho:.2f} (p = {p:.1e}). Mean recovery given coverage: "
              + (f"{np.mean(pos):.0f}% in the {len(pos)} cells with a positive margin" if pos else "no cell has a positive margin")
              + ", " + (f"{np.mean(neg):.0f}% in the {len(neg)} with a margin ≤ 0." if neg else "no cell has a margin ≤ 0.") + "\n")
            for theme in THEMES:
                figure_separation(points, theme)
            w('<picture><source media="(prefers-color-scheme: dark)" srcset="fig_separation_dark.png">'
              '<img alt="Recovery given coverage against the population margin, one point per cell; the same numbers are in the table above." '
              'src="fig_separation_light.png"></picture>\n')

    if errors:
        w("\n## Analysis errors\n")
        for r in errors:
            w(f"- {r['grid']} {r['design']} {r['law']} n={r['n']} seed={r['seed']}: `{r['error'].strip().splitlines()[-1]}`")

    (OUT / "summary.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L))


if __name__ == "__main__":
    main()
