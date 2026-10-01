"""Baselines for the Monte Carlo (README §8.1; Phase 3).

Pure Python: fixed-form IV (oracle and wrong-form 2SLS), sieve 2SLS, kernel IV,
library + sparse IV. With PySR: NPIV -> PySR distillation, control-function SR,
SRIT-style pruning. With torch: DeepIV.
"""

from symiv.baselines.fixed_form import STANDARD_FORMS, fixed_form_iv, oracle_iv, wrong_forms
from symiv.baselines.library_iv import LIBRARY, fit_library_iv
from symiv.baselines.npiv import fit_kiv, fit_sieve_iv

__all__ = [
    "LIBRARY",
    "STANDARD_FORMS",
    "fit_kiv",
    "fit_library_iv",
    "fit_sieve_iv",
    "fixed_form_iv",
    "oracle_iv",
    "wrong_forms",
]
