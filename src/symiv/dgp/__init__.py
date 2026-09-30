"""Data-generating processes: structural laws and Monte Carlo designs (README §8.1)."""

from symiv.dgp.designs import DESIGN_DEFAULTS, Sample, conditional_mean, simulate
from symiv.dgp.laws import LAWS, Law, get_law

__all__ = ["DESIGN_DEFAULTS", "LAWS", "Law", "Sample", "conditional_mean", "get_law", "simulate"]
