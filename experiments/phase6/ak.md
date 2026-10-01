# Phase 6: the Angrist–Krueger (1991) stress test

329,509 men born 1930–39 (1980 census, the Mastering 'Metrics extract). Log weekly wage demeaned within year of birth; x = years of schooling + 1; instruments: quarter-of-birth contrasts. Candidates: plain PySR on a 30,000-observation subsample, PySR distilled from the sieve-2SLS curve, the library path; selection on all observations; the identification report on a 50,000-observation subsample.

## 30 within-cohort QOB contrasts (AK Table V): K = 31

- First-stage F = 4.9. Linear return: OLS 0.071, 2SLS 0.089 (AK: about 0.07 and 0.09).
- Sieve-2SLS curve (J = 5): f(8) = -0.59, f(12) = -0.02, f(16) = 0.38.
- Plain PySR's own pick: `log(0.07511407669269113*x0)`; implied return per year at 9 / 13 / 17 years: 0.100 / 0.071 / 0.056.
- Pooled + MMSC-BIC: `log(0.0751609016420969*x0)`. Pooled + BIC + structure: `log(0.0751609016420969*x0)`; return at 9 / 13 / 17 years: 0.100 / 0.071 / 0.056.
- Linear form, return per year: 0.110; Wald 95% [0.061, 0.159]; AR 95% [-0.013, 0.443].
- **Identification report: weakly identified.** 25 of 25 other candidates are not rejected; the farthest is 1.08 sd from the selected formula. AR/Wald width ratios: 2.1.
  - not rejected (S = 14.6 <= 45.0), 1.08 sd away: -0.0109097389785644*x0**2 + 2.82770305696302*log(x0)**2 - 9.24315605954905*log(x0) + 6.947319
  - not rejected (S = 14.9 <= 45.0), 0.95 sd away: -0.00542247785644888*x0**2 + 0.771155051121936*log(x0)**2 - 4.93220953916309 - 5.042371053521
  - not rejected (S = 23.5 <= 45.0), 0.95 sd away: Max(2.82135342058072 - 2.84677292465429*log(x0), 1.27211389554713*log(0.0741248579269855*x0))
  - not rejected (S = 16.7 <= 45.0), 0.84 sd away: -0.0049218054659635*x0**2 + 0.697543314787077*log(x0)**2 - 4.35038858859347 + 7.6362452971875

## 3 overall QOB contrasts: K = 4

- First-stage F = 34.0. Linear return: OLS 0.071, 2SLS 0.103 (AK: about 0.07 and 0.09).
- Sieve-2SLS curve (J = 4): f(8) = -0.16, f(12) = -1.15, f(16) = 1.38.
- Plain PySR's own pick: `log(0.07510047894511249*x0)`; implied return per year at 9 / 13 / 17 years: 0.100 / 0.071 / 0.056.
- Pooled + MMSC-BIC: `log(0.0751528553152676*x0)`. Pooled + BIC + structure: `log(0.0751528553152676*x0)`; return at 9 / 13 / 17 years: 0.100 / 0.071 / 0.056.
- Linear form, return per year: 0.107; Wald 95% [0.033, 0.181]; AR 95% [-0.009, 0.261].
- **Identification report: weakly identified.** 23 of 23 other candidates are not rejected; the farthest is 1.28 sd from the selected formula. AR/Wald width ratios: 1.5.
  - not rejected (S = 1.7 <= 9.5), 1.28 sd away: -9.99945513366186*sqrt(x0) + 0.0403165933682163*x0**2 + 7.35288867519129*log(x0) + 9.7133433051
  - not rejected (S = 8.7 <= 9.5), 0.72 sd away: -0.360890553462569*exp(-x0)
  - not rejected (S = 8.8 <= 9.5), 0.72 sd away: -0.147517293817511/x0**x0
  - not rejected (S = 8.7 <= 9.5), 0.72 sd away: -0.324156731940297*exp(-x0**0.94000205684948)

