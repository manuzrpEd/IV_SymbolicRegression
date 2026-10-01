# Phase 6: Engel curves on the FES 1995 extract of Blundell, Chen & Kristensen (2007)

Source: `data\engel95.csv`: the `Engel95` data of the R package `np` (FES 1995; BCK 2007), 1655 couples, 628 without children and 1027 with; instrument `logwages`. Candidates: plain PySR, PySR distilled from the sieve-2SLS curve, the library path and the template library, pooled; selection by BIC + structure (w = 0.5); K spline instruments in the head's log earnings. 'Search only' is the same selection without the templates. The S tests are Proposition 5's (χ² with K degrees of freedom, valid without a rank condition); the AR interval for the quadratic term is the projection interval around the S minimizer. Shape: the selected curve at the 10th, 50th and 90th percentiles of log expenditure.

## All couples (n = 1655, K = 12)

| Share | First-stage F | Selected: pooled + BIC + structure | Search only | Within the confidence set | Shape | Identification | Working–Leser: S | Quadratic: S | Quadratic term c: estimate, AR 95% interval |
|---|---|---|---|---|---|---|---|---|---|
| food | 59 | `0.746666424964737**x0` (plain+distill) | same | same | decreasing | weakly identified (24/25 not rejected, farthest 0.69 sd) | 9.4 vs 21.0: not rejected | 8.4 vs 21.0: not rejected | -0.020, [-0.115, 0.061] |
| catering | 59 | `0.0797619321596834` (plain+distill) | same | same | flat | weakly identified (28/28 not rejected, farthest 0.92 sd) | 19.0 vs 21.0: not rejected | 14.9 vs 21.0: not rejected | -0.024, [-0.053, 0.008] |
| alcohol | 59 | `0.192381705901772 - 0.0248741031811344*x0` (templates) | `0.122902106771108 - 0.00220878005299157*x0**2` | same | decreasing | weakly identified (27/34 not rejected, farthest 0.83 sd) | 13.1 vs 21.0: not rejected | 11.5 vs 21.0: not rejected | -0.015, [-0.069, 0.021] |
| fuel | 59 | `log(x0)**(-5.30977113847952)` (distill) | same | same | decreasing | weakly identified (27/31 not rejected, farthest 0.33 sd) | 16.6 vs 21.0: not rejected | 6.9 vs 21.0: not rejected | 0.026, [-0.005, 0.083] |
| motor | 59 | `0.692608635296206**x0` (plain) | same | `0.0246483229548064/Max(0.165140618779, x0 - 5.74057819725705)` | decreasing | rejected (4/29 not rejected, farthest 1.02 sd) | 29.5 vs 21.0: **rejected** | 16.5 vs 21.0: not rejected | -0.086, [-0.174, -0.031] **excludes 0** |
| fares | 59 | `0.0149397315657459` (plain+distill) | same | `0.00278384597560343*x0` | flat | rejected (36/37 not rejected, farthest 2.13 sd) | 16.5 vs 21.0: not rejected | 13.2 vs 21.0: not rejected | 0.024, [-0.010, 0.088] |
| leisure | 59 | `0.000512596928078178*exp(x0)` (plain) | same | same | increasing | weakly identified (29/34 not rejected, farthest 0.25 sd) | 12.7 vs 21.0: not rejected | 10.9 vs 21.0: not rejected | 0.043, [-0.067, 0.122] |

Details: plain PySR's own pick (the shape of E[share | log expenditure]); the sieve-2SLS curve's J; the AR intervals of the selected formula's constants; the reasons of the identification report.

- **food**: plain PySR picks `0.7472962643672594**x0`; sieve J = 4; MMSC-BIC alone picks `exp(-0.292136746551537*x0)`; AR intervals of the constants: [0.742, 0.751]; S of the selection 11.6 vs 21.0; 117 s.
  - not rejected (S = 6.1 <= 21.0), 0.69 sd away: Max(0.126437875965367, x0*(x0*(0.464913535235961 - 0.0325347364392255*x0) - 2.22702332238546) + 3.810629
  - not rejected (S = 5.5 <= 21.0), 0.49 sd away: x0*(x0*(0.0237361013718118*x0 - 0.41609822803548) + 2.34170951052398) - 4.03506670369486
- **catering**: plain PySR picks `0.033361006980798066/Max(0.40834197215939677, 0.8498357727896769**x0)`; sieve J = 4; MMSC-BIC alone picks `0.0473422431573594*log(x0)`; AR intervals of the constants: [0.0781, 0.0817]; S of the selection 19.4 vs 21.0; 19 s.
  - not rejected (S = 14.8 <= 21.0), 0.92 sd away: 3.30726847090387*sqrt(x0) - 0.0361174541026831*x0**2 - 8.36717230692151 - 7.26245998929715*exp(-x0) + 9
  - not rejected (S = 14.9 <= 21.0), 0.91 sd away: -0.0118624978630428*x0**2 + 1.37433106975557 + 9.99999999999987*exp(-x0) - 5.34236482285764/x0
- **alcohol**: plain PySR picks `exp(x0*(-0.839054602190584) - Max(-2.0435205579015063, 3.694227646017447 - x0))`; sieve J = 4; MMSC-BIC alone picks `0.466960594875053*x0**2*exp(-Max(5.15077371665791, x0))`; AR intervals of the constants: [0.12, 0.278]; [-0.0404, -0.0117]; S of the selection 13.2 vs 21.0; 38 s.
  - not rejected (S = 9.6 <= 21.0), 0.83 sd away: exp(-0.889222634549727*x0 - 2.47434263889177*Max(-0.837372241092358, 4.28096869275032 - x0))
  - not rejected (S = 9.8 <= 21.0), 0.53 sd away: 9.99992696948456*sqrt(x0) + 7.44622647413224*x0**2 + 5.56960574328717*x0*log(x0) - 5.37595692337659*x0 -
- **fuel**: plain PySR picks `0.6023993124834137**x0`; sieve J = 6; MMSC-BIC alone picks `log(x0)**(-5.30977113847952)`; AR intervals of the constants: [-5.38, -5.24]; S of the selection 10.4 vs 21.0; 36 s.
  - not rejected (S = 8.0 <= 21.0), 0.33 sd away: Max(0.0515700362753648, (0.90490536348185**x0)**x0)
  - not rejected (S = 13.6 <= 21.0), 0.30 sd away: Max(x0**(-1.64792816908949), 10.0*exp(-x0))
- **motor**: plain PySR picks `0.6930725065654605**x0`; sieve J = 4; MMSC-BIC alone picks `0.0246483229548064/Max(0.165140618779, x0 - 5.74057819725705)`; AR intervals of the constants: ; S of the selection 34.5 vs 21.0; 33 s.
  - the selected formula fails the moment conditions (S = 34.5 > 21.0)
  - not rejected (S = 14.0 <= 21.0), 1.02 sd away: -0.081929079485034 + 0.153998442352018/Max(0.666462088460048, x0 - 5.15515421048754)
- **fares**: plain PySR picks `x0*0.003084877784529922`; sieve J = 4; MMSC-BIC alone picks `(0.0848236955472833*x0)**x0`; AR intervals of the constants: ; S of the selection 21.3 vs 21.0; 66 s.
  - the selected formula fails the moment conditions (S = 21.3 > 21.0)
  - not rejected (S = 10.8 <= 21.0), 2.13 sd away: -4.12395567443219*sqrt(x0) - 3.80685148470596*x0**2 - 8.30669684293805*x0*log(x0) + 9.99999994930743*x0
- **leisure**: plain PySR picks `exp(x0 - 1*7.592389554911396)`; sieve J = 4; MMSC-BIC alone picks `0.000512596928078178*exp(x0)`; AR intervals of the constants: [0.000479, 0.000544]; S of the selection 13.0 vs 21.0; 31 s.
  - not rejected (S = 7.8 <= 21.0), 0.25 sd away: Max(0.0702731270525132, (x0 - 4.92638643871855)/log(-9.98797997804259*x0 + 1.89936064295777*x0**2.526679
  - not rejected (S = 11.0 <= 21.0), 0.25 sd away: Max(0.0768693080270837, (x0 - 5.00760658034829)/log(9.99999999999953*x0 + 9.99999999999945))

## No children (n = 628, K = 9)

| Share | First-stage F | Selected: pooled + BIC + structure | Search only | Within the confidence set | Shape | Identification | Working–Leser: S | Quadratic: S | Quadratic term c: estimate, AR 95% interval |
|---|---|---|---|---|---|---|---|---|---|
| food | 31 | `-0.27900081820205*x0 + log(x0)` (distill) | same | same | decreasing | weakly identified (22/27 not rejected, farthest 0.36 sd) | 7.5 vs 16.9: not rejected | 5.3 vs 16.9: not rejected | -0.048, [-0.168, 0.072] |
| catering | 31 | `0.0815693309949540` (plain+distill) | same | same | flat | weakly identified (28/28 not rejected, farthest 2.23 sd) | 11.9 vs 16.9: not rejected | 10.8 vs 16.9: not rejected | -0.023, [-0.068, 0.022] |
| alcohol | 31 | `0.0693249785328104` (plain+distill) | same | same | flat | weakly identified (28/30 not rejected, farthest 2.56 sd) | 13.6 vs 16.9: not rejected | 4.8 vs 16.9: not rejected | -0.063, [-0.141, 0.016] |
| fuel | 31 | `0.590354264630509**x0` (plain+distill) | same | same | decreasing | weakly identified (31/32 not rejected, farthest 0.36 sd) | 8.1 vs 16.9: not rejected | 6.6 vs 16.9: not rejected | 0.016, [-0.033, 0.080] |
| motor | 31 | `0.699976879617347**x0` (plain) | same | same | decreasing | weakly identified (25/28 not rejected, farthest 0.85 sd) | 7.3 vs 16.9: not rejected | 4.4 vs 16.9: not rejected | -0.076, [-0.141, -0.010] **excludes 0** |
| fares | 31 | `0.0193665104993335` (plain+distill) | same | same | flat | weakly identified (35/40 not rejected, farthest 2.77 sd) | 11.0 vs 16.9: not rejected | 10.2 vs 16.9: not rejected | 0.055, [-0.036, 0.102] |
| leisure | 31 | `0.000555730225499993*exp(x0)` (plain+distill) | same | same | increasing | weakly identified (20/24 not rejected, farthest 0.25 sd) | 3.8 vs 16.9: not rejected | 2.0 vs 16.9: not rejected | 0.058, [-0.062, 0.178] |

Details: plain PySR's own pick (the shape of E[share | log expenditure]); the sieve-2SLS curve's J; the AR intervals of the selected formula's constants; the reasons of the identification report.

- **food**: plain PySR picks `0.7246899223206379**x0`; sieve J = 5; MMSC-BIC alone picks `-0.27900081820205*x0 + log(x0)`; AR intervals of the constants: [-0.281, -0.277]; S of the selection 6.2 vs 16.9; 55 s.
  - not rejected (S = 4.8 <= 16.9), 0.36 sd away: Max(-1.85102987084653, -1.03261026924816*Max(1.66433324272995, log(x0))) + 1.93595140492059
  - not rejected (S = 4.7 <= 16.9), 0.34 sd away: Max(-1.79521118926621, -0.955663203953849*Max(1.65725254951822, log(x0))) + Max(1.80269794308352, log(x0
- **catering**: plain PySR picks `-1*0.17331562522569444 + 1.5160489069574945/Max(5.876889959474346, x0)`; sieve J = 4; MMSC-BIC alone picks `0.0815693309949540`; AR intervals of the constants: [0.0763, 0.0869]; S of the selection 12.0 vs 16.9; 21 s.
  - not rejected (S = 9.1 <= 16.9), 2.23 sd away: 0.874642453043621*sqrt(x0) - 0.199128232150144*x0**2 + 0.885642754021756*x0*log(x0) - 6.09706306196921 +
  - not rejected (S = 9.7 <= 16.9), 1.27 sd away: 4.4170085253526*sqrt(x0) - 0.0573864703461925*x0**2 - 9.99999999999997 + 9.99999999999993*exp(-x0) + 7.8
- **alcohol**: plain PySR picks `-(x0*0.15650171765214066 - 1.7500219898765181) - 4.465187002621463/x0`; sieve J = 4; MMSC-BIC alone picks `0.0693249785328104`; AR intervals of the constants: [0.0686, 0.072]; S of the selection 16.6 vs 16.9; 19 s.
  - not rejected (S = 3.9 <= 16.9), 2.56 sd away: 2.71041311634851*sqrt(x0) - 0.21146186360051*x0**2 + 0.783876681115969*x0*log(x0) - 9.07822335224053 + 1
  - not rejected (S = 3.9 <= 16.9), 2.52 sd away: x0*(x0*(1.271397498072 - 0.422603580966601*log(x0)) - 3.73250187453555) + 3.95222150791855
- **fuel**: plain PySR picks `0.5926883626242004**x0`; sieve J = 4; MMSC-BIC alone picks `log(x0)**(-5.50258071178836)`; AR intervals of the constants: [0.583, 0.597]; S of the selection 8.0 vs 16.9; 39 s.
  - not rejected (S = 6.3 <= 16.9), 0.36 sd away: 0.789066748592971*log(x0)**2 - 2.87556239134725*log(x0) + 2.65845875071915
  - not rejected (S = 6.0 <= 16.9), 0.29 sd away: 0.00377076620797035*x0**2 - 0.032787892331952*x0 + 0.0759682145170781 + 10.0*exp(-x0)
- **motor**: plain PySR picks `(x0*21.023318375815606 - 79.40890665502387)/exp(x0)`; sieve J = 4; MMSC-BIC alone picks `0.794177928396066/x0`; AR intervals of the constants: [0.69, 0.71]; S of the selection 8.4 vs 16.9; 20 s.
  - not rejected (S = 11.3 <= 16.9), 0.85 sd away: Max(0.148892673789073, (x0*(9.99999999 - 5.41437469184815*x0) - 9.99999999)*exp(-x0))
  - not rejected (S = 11.3 <= 16.9), 0.85 sd away: 0.148892673788923
- **fares**: plain PySR picks `23.245785266016775/(1348.2661197882292 - exp(x0))`; sieve J = 5; MMSC-BIC alone picks `8.25706476878557e-5*exp(x0)`; AR intervals of the constants: [0.0172, 0.0223]; S of the selection 15.2 vs 16.9; 38 s.
  - not rejected (S = 8.4 <= 16.9), 2.77 sd away: 1.16654041665505*log(x0)**2 - 3.87105769376292*log(x0) + 3.22238550127351
  - not rejected (S = 8.0 <= 16.9), 2.60 sd away: -7.7060032672285*sqrt(x0) - 0.0151480635543267*x0*log(x0) + 2.81763742807346*log(x0)**2 + 9.999999999999
- **leisure**: plain PySR picks `exp(x0)*0.0005564168326433054`; sieve J = 4; MMSC-BIC alone picks `0.000555730225499993*exp(x0)`; AR intervals of the constants: [0.000479, 0.000635]; S of the selection 2.1 vs 16.9; 18 s.
  - not rejected (S = 4.2 <= 16.9), 0.25 sd away: 0.742231378613019*log(x0) - 1.11094802301091
  - not rejected (S = 3.8 <= 16.9), 0.21 sd away: 0.138148480869549*x0 - 0.607988985554495

## With children (n = 1027, K = 10)

| Share | First-stage F | Selected: pooled + BIC + structure | Search only | Within the confidence set | Shape | Identification | Working–Leser: S | Quadratic: S | Quadratic term c: estimate, AR 95% interval |
|---|---|---|---|---|---|---|---|---|---|
| food | 45 | `0.759543456659386**x0` (plain+distill) | same | same | decreasing | weakly identified (32/33 not rejected, farthest 0.44 sd) | 5.8 vs 18.3: not rejected | 5.8 vs 18.3: not rejected | -0.002, [-0.060, 0.055] |
| catering | 45 | `0.0783431280464914` (plain+distill) | same | same | flat | weakly identified (27/28 not rejected, farthest 1.58 sd) | 11.3 vs 18.3: not rejected | 9.5 vs 18.3: not rejected | -0.025, [-0.076, 0.008] |
| alcohol | 45 | `x0**(-1.79453231830045)` (distill) | same | same | decreasing | weakly identified (30/33 not rejected, farthest 1.06 sd) | 14.0 vs 18.3: not rejected | 14.0 vs 18.3: not rejected | -0.000, [-0.028, 0.056] |
| fuel | 45 | `log(x0)**(-5.20028577852749)` (distill) | same | same | decreasing | weakly identified (31/34 not rejected, farthest 0.37 sd) | 18.4 vs 18.3: **rejected** | 4.7 vs 18.3: not rejected | 0.036, [0.000, 0.084] **excludes 0** |
| motor | 45 | `0.687855019062617**x0` (plain+distill) | same | `0.0166602261286412/Max(0.115582167827718, x0 - 5.77741753402261)` | decreasing | rejected (16/30 not rejected, farthest 1.24 sd) | 25.8 vs 18.3: **rejected** | 13.1 vs 18.3: not rejected | -0.196, [-0.256, -0.078] **excludes 0** |
| fares | 45 | `4.74143132927502e-5*exp(x0)` (distill) | same | same | increasing | weakly identified (40/44 not rejected, farthest 1.43 sd) | 13.4 vs 18.3: not rejected | 10.6 vs 18.3: not rejected | 0.045, [-0.015, 0.146] |
| leisure | 45 | `0.00048568426478055*exp(x0)` (plain) | same | same | increasing | weakly identified (29/33 not rejected, farthest 0.38 sd) | 9.8 vs 18.3: not rejected | 9.0 vs 18.3: not rejected | 0.040, [-0.062, 0.142] |

Details: plain PySR's own pick (the shape of E[share | log expenditure]); the sieve-2SLS curve's J; the AR intervals of the selected formula's constants; the reasons of the identification report.

- **food**: plain PySR picks `0.7604682825376219**x0`; sieve J = 4; MMSC-BIC alone picks `log(x0)**(-2.85495014936732)`; AR intervals of the constants: [0.754, 0.765]; S of the selection 7.2 vs 18.3; 36 s.
  - not rejected (S = 4.4 <= 18.3), 0.44 sd away: Max(2.56706932292566, x0 - 2.73127386502764)**(-1.45772960834387)
  - not rejected (S = 4.4 <= 18.3), 0.44 sd away: Max(2.56518190174827, -0.00869678281028173*x0, x0 - 2.73316019999771)**(-1.45864875172439)
- **catering**: plain PySR picks `-0.20058243384783664*x0 + 1.1398648954565629*log(x0) - 0.7577502094239483`; sieve J = 4; MMSC-BIC alone picks `0.046372695870019*log(x0)`; AR intervals of the constants: [0.0742, 0.083]; S of the selection 11.9 vs 18.3; 24 s.
  - not rejected (S = 6.9 <= 18.3), 1.58 sd away: -7.60084670523376*sqrt(x0) - 8.28437532098235*x0**2 + 0.329029059886909*x0*log(x0) + 8.86004357204784*x0
  - not rejected (S = 7.3 <= 18.3), 1.24 sd away: -9.99999997544064*sqrt(x0) - 0.397426519372389*x0**2 + 2.54310635057859*x0*log(x0) + 9.88402303366797 + 
- **alcohol**: plain PySR picks `0.08911950035719386/(-x0 + Max(5.293827095532389, x0) + 1.7143849633292283)`; sieve J = 4; MMSC-BIC alone picks `x0**(-1.79453231830045)`; AR intervals of the constants: [-1.83, -1.75]; S of the selection 14.7 vs 18.3; 34 s.
  - not rejected (S = 12.5 <= 18.3), 1.06 sd away: 0.138561248385784/(Max(x0, 3.85710799107173 - log(x0 - 4.45479674587321)) - 2.57349579684861)
  - not rejected (S = 14.4 <= 18.3), 0.55 sd away: -3.41447385642893*sqrt(x0) + 0.122305787045639*x0**2 - 2.86557746383786*x0*log(x0) + 9.99999998721823*x
- **fuel**: plain PySR picks `0.6082422436241917**x0`; sieve J = 6; MMSC-BIC alone picks `log(x0)**(-5.20028577852749)`; AR intervals of the constants: [-5.27, -5.13]; S of the selection 10.3 vs 18.3; 25 s.
  - not rejected (S = 4.1 <= 18.3), 0.37 sd away: 9.99999999749308*sqrt(x0) - 0.562418003352918*x0**2 + 6.50592462866435*x0*log(x0) - 9.89073998427132*x0 
  - not rejected (S = 4.2 <= 18.3), 0.35 sd away: 8.66480883977833*sqrt(x0) + 9.10986687406419*x0**2 + 2.49709600536568*x0*log(x0) - 8.21444360299638*x0 -
- **motor**: plain PySR picks `0.6878555589096563**x0`; sieve J = 4; MMSC-BIC alone picks `0.0166602261286412/Max(0.115582167827718, x0 - 5.77741753402261)`; AR intervals of the constants: ; S of the selection 32.8 vs 18.3; 35 s.
  - the selected formula fails the moment conditions (S = 32.8 > 18.3)
  - not rejected (S = 14.6 <= 18.3), 1.24 sd away: -9.99999994012591*sqrt(x0) + 0.0302742502749517*x0**2 + 8.16361498643366*log(x0) + 9.99999991199622 - 9
- **fares**: plain PySR picks `x0*0.002531867753509057`; sieve J = 4; MMSC-BIC alone picks `4.74143132927502e-5*exp(x0)`; AR intervals of the constants: [3.99e-05, 5.69e-05]; S of the selection 13.9 vs 18.3; 46 s.
  - not rejected (S = 3.6 <= 18.3), 1.43 sd away: x0*(x0*(0.909008211454973 - 0.0519158883410586*x0) - 5.2461400398159) + 9.99999888847122
  - not rejected (S = 12.1 <= 18.3), 1.26 sd away: 0.0161458189709655*x0**2 - 0.170756763510774*x0 + 0.460144280259342
- **leisure**: plain PySR picks `exp(x0)*0.00047336598275796854`; sieve J = 4; MMSC-BIC alone picks `0.00048568426478055*exp(x0)`; AR intervals of the constants: [0.000447, 0.00052]; S of the selection 11.4 vs 18.3; 38 s.
  - not rejected (S = 15.1 <= 18.3), 0.38 sd away: log(x0) - 1.56689673745034
  - not rejected (S = 7.1 <= 18.3), 0.30 sd away: Max(1.65014788736235 - log(x0), log(x0 - 0.342109310426109) - 1.51573212043705)

