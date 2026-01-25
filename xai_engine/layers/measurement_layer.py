"""
Measurement Layer (الإعراب / القياس) - Layer 4

Purpose: Apply operators and perform measurement
Output: MeasurementTrace

This is the CRITICAL LAYER in XAI.

This layer:
- Detects governors (operators)
- Applies Trigger → Scope → Effect
- Assigns measurements (case marks, truth values, etc.)
- Resolves conflicts using constraints

NO OPERATOR → NO MEASUREMENT → NO JUDGMENT

This is where final meaning selection happens through measurement.
"""

from typing import Any, Dict, List, Optional
from .base import LayerBase
from ..core.output_objects import (
    RelationGraph,
    MeasurementTrace,
    Operator,
    RelationType,
)
from ..core.domain import Domain
import uuid


class MeasurementLayer(LayerBase):
    """
    Layer 4: Measurement through operators
    
    This layer applies operators to perform measurements.
    Without measurement, no judgment can be formed.
    """
    
    def __init__(self, domain: Domain):
        super().__init__("measurement", domain)
        self.operators_catalog = domain.operators_catalog
    
    def process(self, input_data: Dict[str, Any]) -> MeasurementTrace:
        """
        Apply measurements using operators
        
        Args:
            input_data: Dict with "relation_graph" and "semantic_candidates"
            
        Returns:
            MeasurementTrace documenting all measurements
        """
        self.validate_input(input_data, "relational")
        
        relation_graph = input_data["relation_graph"]
        semantic_candidates = input_data["semantic_candidates"]
        
        self.log_operation("start_measurement", {
            "relations_count": len(relation_graph.relations)
        })
        
        # Enforce: no judgment without relation
        self.constraints.no_judgment_without_relation(
            judgment="measurement_process",
            relations=relation_graph.relations
        )
        
        # Detect operators
        operators = self._detect_operators(relation_graph, semantic_candidates)
        self.log_operation("operators_detected", {"count": len(operators)})
        
        # Enforce: no measurement without operator
        if not operators:
            from ..core.constraints import ConstraintViolation
            raise ConstraintViolation(
                "NO_MEASUREMENT_WITHOUT_OPERATOR",
                "Cannot perform measurement without operators.\n"
                "Operators (governors, rules) are required for all measurements.",
                {"relations": len(relation_graph.relations)}
            )
        
        # Apply operators
        applications = self._apply_operators(operators, semantic_candidates)
        self.log_operation("operators_applied", {"applications": len(applications)})
        
        # Detect and resolve conflicts
        conflicts = self._detect_conflicts(applications)
        self.log_operation("conflicts_detected", {"count": len(conflicts)})
        
        # Resolve conflicts
        if conflicts:
            applications = self._resolve_conflicts(conflicts, applications)
            self.log_operation("conflicts_resolved", {"remaining": len(conflicts)})
        
        # Generate final assignments
        final_assignments = self._generate_final_assignments(applications)
        
        measurement_id = f"MEAS_{uuid.uuid4().hex[:8].upper()}"
        
        return MeasurementTrace(
            measurement_id=measurement_id,
            operators=operators,
            applications=applications,
            conflicts=conflicts,
            final_assignments=final_assignments,
        )
    
    def _detect_operators(
        self,
        relation_graph: RelationGraph,
        semantic_candidates: List[Any]
    ) -> List[Operator]:
        """
        Detect operators (governors) from relations
        
        Operators cause effects on their scope:
        - Verbs govern subjects and objects
        - Particles govern nouns
        - Implicit operators (missing but understood)
        """
        operators = []
        
        for relation in relation_graph.relations:
            operator = self._create_operator_from_relation(relation)
            if operator:
                operators.append(operator)
        
        # Add implicit operators if needed
        implicit_ops = self._detect_implicit_operators(relation_graph)
        operators.extend(implicit_ops)
        
        return operators
    
    def _create_operator_from_relation(
        self,
        relation: Dict[str, Any]
    ) -> Optional[Operator]:
        """
        Create an operator from a relation
        """
        relation_type = relation.get("relation_type")
        
        if relation_type == RelationType.ISNAD.value:
            # Predication: predicate is the operator
            return Operator(
                operator_id=f"OP_{relation['relation_id']}",
                operator_type="predicate",
                trigger=relation.get("predicate", ""),
                scope=[relation.get("subject", "")],
                effect="nominative_case",  # Marfu'
                relation_type=RelationType.ISNAD,
            )
        
        elif relation_type == RelationType.TAQYEED.value:
            # Restriction: governor restricts dependent
            return Operator(
                operator_id=f"OP_{relation['relation_id']}",
                operator_type="particle",
                trigger=relation.get("governor", ""),
                scope=[relation.get("dependent", "")],
                effect="genitive_case",  # Majrur
                relation_type=RelationType.TAQYEED,
            )
        
        return None
    
    def _detect_implicit_operators(
        self,
        relation_graph: RelationGraph
    ) -> List[Operator]:
        """
        Detect implicit operators (محذوف مقدّر)
        
        Some structures require implicit operators.
        """
        implicit_operators = []
        
        # Example: implicit "كان" in nominal sentences
        if relation_graph.discourse_type.value == "assertive":
            # Check if we need implicit copula
            if relation_graph.primary_predication:
                pred = relation_graph.primary_predication
                implicit_operators.append(
                    Operator(
                        operator_id=f"OP_IMPLICIT_COPULA",
                        operator_type="implicit_verb",
                        trigger="كان_محذوف",
                        scope=[pred.get("subject", ""), pred.get("predicate", "")],
                        effect="maintain_case",
                        relation_type=RelationType.ISNAD,
                        conditions=["nominal_sentence"],
                    )
                )
        
        return implicit_operators
    
    def _apply_operators(
        self,
        operators: List[Operator],
        semantic_candidates: List[Any]
    ) -> List[Dict[str, Any]]:
        """
        Apply each operator to its scope
        
        Operator application:
        1. Check trigger condition
        2. Identify scope
        3. Apply effect
        4. Record application
        """
        applications = []
        
        for operator in operators:
            # Check if operator applies
            if self._check_trigger(operator):
                # Apply to each element in scope
                for target in operator.scope:
                    application = {
                        "application_id": f"APP_{len(applications):04d}",
                        "operator_id": operator.operator_id,
                        "target": target,
                        "effect": operator.effect,
                        "timestamp": self._get_timestamp(),
                    }
                    applications.append(application)
                    
                    self.log_operation("operator_applied", {
                        "operator": operator.operator_id,
                        "target": target,
                        "effect": operator.effect,
                    })
        
        return applications
    
    def _check_trigger(self, operator: Operator) -> bool:
        """Check if operator's trigger condition is met"""
        # In production, check actual conditions
        # For now, always true
        return True
    
    def _detect_conflicts(
        self,
        applications: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Detect conflicts between operator applications
        
        Conflicts occur when:
        - Multiple operators affect the same target
        - Contradictory effects
        """
        conflicts = []
        
        # Group applications by target
        targets = {}
        for app in applications:
            target = app["target"]
            if target not in targets:
                targets[target] = []
            targets[target].append(app)
        
        # Detect conflicts
        for target, apps in targets.items():
            if len(apps) > 1:
                # Multiple operators on same target
                effects = [a["effect"] for a in apps]
                if len(set(effects)) > 1:
                    # Contradictory effects
                    conflicts.append({
                        "conflict_id": f"CONF_{len(conflicts):03d}",
                        "target": target,
                        "applications": [a["application_id"] for a in apps],
                        "conflicting_effects": effects,
                        "resolution": "pending",
                    })
        
        return conflicts
    
    def _resolve_conflicts(
        self,
        conflicts: List[Dict[str, Any]],
        applications: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Resolve conflicts using constraint rules
        
        Resolution strategies:
        - Precedence (which operator is stronger)
        - Proximity (which is closer)
        - Domain-specific rules
        """
        for conflict in conflicts:
            # Apply resolution strategy
            # For now, use simple precedence
            conflict_apps = [
                a for a in applications 
                if a["application_id"] in conflict["applications"]
            ]
            
            # Keep first application, mark others as overridden
            if conflict_apps:
                winner = conflict_apps[0]
                for app in conflict_apps[1:]:
                    app["overridden"] = True
                    app["overridden_by"] = winner["application_id"]
                
                conflict["resolution"] = "resolved_by_precedence"
                conflict["winner"] = winner["application_id"]
        
        return applications
    
    def _generate_final_assignments(
        self,
        applications: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """
        Generate final measurement assignments
        
        Returns a mapping of targets to their final measurements.
        """
        assignments = {}
        
        for app in applications:
            # Skip overridden applications
            if app.get("overridden", False):
                continue
            
            target = app["target"]
            effect = app["effect"]
            
            assignments[target] = {
                "measurement": effect,
                "operator": app["operator_id"],
                "application": app["application_id"],
            }
        
        return assignments
    
    def _get_timestamp(self) -> str:
        """Get current timestamp"""
        from datetime import datetime
        return datetime.utcnow().isoformat()
