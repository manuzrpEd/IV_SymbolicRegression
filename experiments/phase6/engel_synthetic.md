# Phase 6: Engel curves on the FES 1995 extract of Blundell, Chen & Kristensen (2007)

Source: synthetic FES-like data with the planted food share 0.45 − 0.06 log x (a pipeline test, not evidence). Candidates: plain PySR, PySR distilled from the sieve-2SLS curve, the library path and the template library, pooled; selection by BIC + structure (w = 0.5); K spline instruments in the head's log earnings. 'Search only' is the same selection without the templates. The S tests are Proposition 5's (χ² with K degrees of freedom, valid without a rank condition); the AR interval for the quadratic term is the projection interval around the S minimizer. Shape: the selected curve at the 10th, 50th and 90th percentiles of log expenditure.

## All couples (n = 1500, K = 11)

| Share | First-stage F | Selected: pooled + BIC + structure | Search only | Shape | Identification | Working–Leser: S | Quadratic: S | Quadratic term c: estimate, AR 95% interval |
|---|---|---|---|---|---|---|---|---|
| food | 180 | `0.452282766951693 - 0.059998108879681*x0` (distill+templates) | same | decreasing | identified (24/30 not rejected, farthest 0.09 sd) | 13.1 vs 19.7: not rejected | 12.8 vs 19.7: not rejected | -0.006, [-0.019, 0.017] |

Details: plain PySR's own pick (the shape of E[share | log expenditure]); the sieve-2SLS curve's J; the AR intervals of the selected formula's constants; the reasons of the identification report.

- **food**: plain PySR picks `0.6828215258793517**x0`; sieve J = 5; MMSC-BIC alone picks `0.452282766951693 - 0.059998108879681*x0`; AR intervals of the constants: [0.418, 0.495]; [-0.0678, -0.0537]; S of the selection 13.1 vs 19.7; 336 s.

