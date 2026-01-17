"""
FractalHub Kernel v1.2

Core kernel components for consciousness processing.
"""

from fractalhub.kernel.version import get_version_metadata, KERNEL_VERSION, API_VERSION
from fractalhub.kernel.trace import Trace, TraceManager
from fractalhub.kernel.gates import Gate, GateType, gate_registry, FourConditions
from fractalhub.kernel.codec import FormCodec, MeaningCodec

__all__ = [
    "get_version_metadata",
    "KERNEL_VERSION",
    "API_VERSION",
    "Trace",
    "TraceManager",
    "Gate",
    "GateType",
    "gate_registry",
    "FourConditions",
    "FormCodec",
    "MeaningCodec",
]
