"""
FractalHub: Fractal Consciousness Kernel v1.2

A consciousness platform implementing Al-Nabhani's Theory of Thinking
with complete separation between signifier and signified.

Core Architecture:
- C0: Phonological Layer
- C1: Signifier Graph (form only, no meaning)
- C2: Gate & Trace System (documented passages)
- C3: Signified Graph (meaning with provenance)

Locked Architecture Invariants:
- NO C3 without C2 trace
- NO C2 without C1 four conditions
- NO meaning without prior_ids evidence
- Strict layer separation
"""

__version__ = "1.2.0"
__kernel_version__ = "1.2"
__api_version__ = "1.2.0"

from fractalhub.kernel import (
    Trace,
    Gate,
    FormCodec,
    get_version_metadata,
)

__all__ = [
    "Trace",
    "Gate",
    "FormCodec",
    "get_version_metadata",
    "__version__",
    "__kernel_version__",
    "__api_version__",
]
