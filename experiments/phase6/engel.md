# Phase 6: Engel curves

Source: synthetic FES-like data (pipeline test, not evidence); n = 1500; K = 11 spline instruments in the head's log earnings. True curve: `0.45 - 0.06*x0`.

- Plain PySR's own pick: `0.6827789802648598**x0`.
- Sieve-2SLS curve: J = 5.
- Pooled + MMSC-BIC: `0.452282766952895 - 0.0599981088799077*x0`.
- **Pooled + BIC + structure: `0.452282766952895 - 0.0599981088799077*x0`**.
- **Identification report: identified**; first-stage F = 180.2; 20 of 25 other candidates not rejected, farthest 0.05 sd away.
- Parametric forms, with their S tests (chi^2 with K degrees of freedom; valid without a rank condition):
  - Working–Leser a + b log x: `0.452282766898926 - 0.0599981088699702*x0`; J = 13.0 on 9 df; S = 13.1 vs 19.7: not rejected.
  - quadratic a + b log x + c (log x)^2: `-0.00555211666759825*x0**2 + 0.000229474762670459*x0 + 0.290049278134154`; J = 12.1 on 8 df; S = 12.8 vs 19.7: not rejected.
