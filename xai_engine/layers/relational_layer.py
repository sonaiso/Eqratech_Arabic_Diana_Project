"""
Relational Layer (النِّسب) - Layer 3

Purpose: Build relations between elements
Output: RelationGraph

This layer:
- Identifies Isnad (predication) relations
- Identifies Taqyeed (restriction) relations
- Identifies Tadmeen (inclusion) relations
- Detects discourse type (Khabar/Insha)

WITHOUT RELATIONS, NO JUDGMENT IS POSSIBLE.
"""

from typing import Any, Dict, List
from .base import LayerBase
from ..core.output_objects import (
    ParseTree,
    SemanticCandidates,
    RelationGraph,
    RelationType,
    DiscourseType,
)
from ..core.domain import Domain


class RelationalLayer(LayerBase):
    """
    Layer 3: Relational structure
    
    Builds the network of relations that enable judgment formation.
    """
    
    def __init__(self, domain: Domain):
        super().__init__("relational", domain)
    
    def process(self, input_data: Dict[str, Any]) -> RelationGraph:
        """
        Build relational structure from form and semantics
        
        Args:
            input_data: Dict with "parse_tree" and "semantic_candidates"
            
        Returns:
            RelationGraph with all relations
        """
        self.validate_input(input_data, "semantic")
        
        parse_tree = input_data["parse_tree"]
        semantic_candidates = input_data["semantic_candidates"]
        
        self.log_operation("start_relational_analysis", {
            "token_count": len(semantic_candidates)
        })
        
        # Build relations
        relations = self._build_relations(parse_tree, semantic_candidates)
        
        # Detect discourse type
        discourse_type = self._detect_discourse_type(parse_tree, relations)
        
        # Identify primary predication (if any)
        primary_predication = self._identify_primary_predication(relations)
        
        # Extract restrictions
        restrictions = self._extract_restrictions(relations)
        
        self.log_operation("relational_analysis_complete", {
            "relations_count": len(relations),
            "discourse_type": discourse_type.value,
        })
        
        return RelationGraph(
            relations=relations,
            discourse_type=discourse_type,
            primary_predication=primary_predication,
            restrictions=restrictions,
        )
    
    def _build_relations(
        self,
        parse_tree: ParseTree,
        semantic_candidates: List[SemanticCandidates]
    ) -> List[Dict[str, Any]]:
        """
        Build relations between tokens
        
        Relations types:
        - Isnad (إسناد): Predication (subject-predicate)
        - Taqyeed (تقييد): Restriction (modifiers, complements)
        - Tadmeen (تضمين): Inclusion (embedded clauses)
        """
        relations = []
        
        # Get POS tags for relation detection
        pos_tags = {p["token_id"]: p["pos"] for p in parse_tree.pos_tags}
        
        # Detect Isnad (predication)
        isnad_relations = self._detect_isnad(semantic_candidates, pos_tags)
        relations.extend(isnad_relations)
        
        # Detect Taqyeed (restriction)
        taqyeed_relations = self._detect_taqyeed(semantic_candidates, pos_tags)
        relations.extend(taqyeed_relations)
        
        # Detect Tadmeen (inclusion)
        tadmeen_relations = self._detect_tadmeen(semantic_candidates, parse_tree)
        relations.extend(tadmeen_relations)
        
        return relations
    
    def _detect_isnad(
        self,
        semantic_candidates: List[SemanticCandidates],
        pos_tags: Dict[str, str]
    ) -> List[Dict[str, Any]]:
        """
        Detect predication relations (subject-predicate)
        
        In Arabic: المبتدأ والخبر، الفاعل والفعل
        """
        isnad_relations = []
        
        # Simplified detection: look for noun-verb or noun-noun patterns
        for i in range(len(semantic_candidates) - 1):
            current = semantic_candidates[i]
            next_token = semantic_candidates[i + 1]
            
            current_pos = pos_tags.get(current.token_id, "")
            next_pos = pos_tags.get(next_token.token_id, "")
            
            # Noun followed by verb or noun (simple predication)
            if current_pos == "noun" and next_pos in ["verb", "noun"]:
                isnad_relations.append({
                    "relation_id": f"ISNAD_{i:03d}",
                    "relation_type": RelationType.ISNAD.value,
                    "subject": current.token_id,
                    "predicate": next_token.token_id,
                    "confidence": 0.7,
                })
        
        return isnad_relations
    
    def _detect_taqyeed(
        self,
        semantic_candidates: List[SemanticCandidates],
        pos_tags: Dict[str, str]
    ) -> List[Dict[str, Any]]:
        """
        Detect restriction relations (modifiers, adjuncts)
        
        Examples: prepositional phrases, adjectives, adverbs
        """
        taqyeed_relations = []
        
        for i in range(len(semantic_candidates) - 1):
            current = semantic_candidates[i]
            next_token = semantic_candidates[i + 1]
            
            current_pos = pos_tags.get(current.token_id, "")
            next_pos = pos_tags.get(next_token.token_id, "")
            
            # Particle followed by noun (prepositional phrase)
            if current_pos == "particle" and next_pos == "noun":
                taqyeed_relations.append({
                    "relation_id": f"TAQYEED_{i:03d}",
                    "relation_type": RelationType.TAQYEED.value,
                    "governor": current.token_id,
                    "dependent": next_token.token_id,
                    "restriction_type": "prepositional",
                    "confidence": 0.8,
                })
        
        return taqyeed_relations
    
    def _detect_tadmeen(
        self,
        semantic_candidates: List[SemanticCandidates],
        parse_tree: ParseTree
    ) -> List[Dict[str, Any]]:
        """
        Detect inclusion relations (embedded structures)
        
        Examples: subordinate clauses, quotations
        """
        tadmeen_relations = []
        
        # Simplified: detect potential embedded structures
        # In production, use syntactic parser
        
        for i, candidate in enumerate(semantic_candidates):
            # Look for embedding markers
            if any("embedded" in c.get("sense", "") for c in candidate.candidates):
                tadmeen_relations.append({
                    "relation_id": f"TADMEEN_{i:03d}",
                    "relation_type": RelationType.TADMEEN.value,
                    "container": candidate.token_id,
                    "embedded": f"CLAUSE_{i}",
                    "confidence": 0.6,
                })
        
        return tadmeen_relations
    
    def _detect_discourse_type(
        self,
        parse_tree: ParseTree,
        relations: List[Dict[str, Any]]
    ) -> DiscourseType:
        """
        Detect discourse type
        
        Types:
        - Khabar (خبر): Assertive/declarative
        - Insha (إنشاء): Imperative, prohibition, interrogation, negation, emphasis
        """
        # Check for discourse markers
        text = parse_tree.text.lower()
        
        # Interrogative markers
        if any(marker in text for marker in ["هل", "ما", "من", "متى", "أين", "كيف", "؟"]):
            return DiscourseType.ISTIFHAM
        
        # Imperative indicators (command verbs)
        if any(marker in text for marker in ["افعل", "قم", "اذهب"]):
            return DiscourseType.AMKR
        
        # Prohibition markers
        if any(marker in text for marker in ["لا تفعل", "لا ت"]):
            return DiscourseType.NAHY
        
        # Negation markers
        if any(marker in text for marker in ["لا", "ليس", "ما"]):
            return DiscourseType.NAFY
        
        # Emphasis markers
        if any(marker in text for marker in ["إن", "أن", "قد", "لام التوكيد"]):
            return DiscourseType.TAWKID
        
        # Default: assertive (khabar)
        return DiscourseType.KHABAR
    
    def _identify_primary_predication(
        self,
        relations: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """
        Identify the main predication relation
        
        Returns the primary Isnad relation if any.
        """
        isnad_relations = [
            r for r in relations 
            if r.get("relation_type") == RelationType.ISNAD.value
        ]
        
        if isnad_relations:
            # Return the first (main) predication
            return isnad_relations[0]
        
        return None
    
    def _extract_restrictions(
        self,
        relations: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Extract all restriction relations
        
        Returns all Taqyeed relations.
        """
        return [
            r for r in relations 
            if r.get("relation_type") == RelationType.TAQYEED.value
        ]
