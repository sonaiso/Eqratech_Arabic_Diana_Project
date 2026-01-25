"""
Core components of the XAI Engine
"""

from .domain import Domain, DomainType
from .constraints import GlobalConstraints
from .output_objects import (
    ParseTree,
    RelationGraph,
    MeasurementTrace,
    JudgmentObject,
    EpistemicWeight,
    ExplanationReport,
    BeforeAfterChain,
)
from .explanatory_schema import (
    ExplanatoryReport,
    ExecutiveSummary,
    LayerTrace,
    FailurePoint,
    ScopeDefinition,
    GovernanceAnnotation,
)
from .report_generator import ReportGenerator

__all__ = [
    "Domain",
    "DomainType",
    "GlobalConstraints",
    "ParseTree",
    "RelationGraph",
    "MeasurementTrace",
    "JudgmentObject",
    "EpistemicWeight",
    "ExplanationReport",
    "BeforeAfterChain",
    "ExplanatoryReport",
    "ExecutiveSummary",
    "LayerTrace",
    "FailurePoint",
    "ScopeDefinition",
    "GovernanceAnnotation",
    "ReportGenerator",
]
