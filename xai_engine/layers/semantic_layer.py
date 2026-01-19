"""
Semantic Layer (المدلول) - Layer 2

Purpose: Generate meaning CANDIDATES without final selection
Output: List of SemanticCandidates

This layer:
- Generates possible meanings for each token
- Classifies denotation types (Mutabaqa/Tadammun/Iltizam)
- Identifies concept types (Entity/Event/Relation/Modality/Value)

NO SELECTION YET. Selection happens with measurement in Layer 4.
"""

from typing import Any, Dict, List
from .base import LayerBase
from ..core.output_objects import ParseTree, SemanticCandidates
from ..core.domain import Domain


class SemanticLayer(LayerBase):
    """
    Layer 2: Semantic candidate generation
    
    Produces multiple possible meanings for each form.
    Final selection requires measurement (Layer 4).
    """
    
    def __init__(self, domain: Domain):
        super().__init__("semantic", domain)
        self.lexicon = {}  # Would be loaded from dictionary
    
    def process(self, input_data: ParseTree) -> List[SemanticCandidates]:
        """
        Generate semantic candidates from form analysis
        
        Args:
            input_data: ParseTree from Form Layer
            
        Returns:
            List of SemanticCandidates (one per token)
        """
        self.validate_input(input_data, "form")
        
        self.log_operation("start_semantic_analysis", {
            "token_count": len(input_data.tokens)
        })
        
        # Enforce constraint: no meaning without form
        self.constraints.no_meaning_without_form(
            meaning="semantic_candidates",
            form=input_data
        )
        
        candidates_list = []
        
        for token in input_data.tokens:
            candidates = self._generate_candidates(token, input_data)
            candidates_list.append(candidates)
        
        self.log_operation("semantic_analysis_complete", {
            "candidates_generated": len(candidates_list)
        })
        
        return candidates_list
    
    def _generate_candidates(self, token: Dict[str, Any], parse_tree: ParseTree) -> SemanticCandidates:
        """
        Generate meaning candidates for a single token
        
        Returns multiple possible meanings, classified by denotation type.
        """
        surface = token["surface"]
        token_id = token["token_id"]
        
        # Get morphology for this token
        token_morphology = next(
            (m for m in parse_tree.morphology["forms"] if m["token_id"] == token_id),
            {}
        )
        
        # Get POS for this token
        token_pos = next(
            (p for p in parse_tree.pos_tags if p["token_id"] == token_id),
            {}
        )
        
        # Generate candidates based on lexicon lookup
        # In production, query actual dictionary/corpus
        candidates = self._lookup_lexicon(surface, token_morphology, token_pos)
        
        # Classify denotation types
        denotation_types = self._classify_denotation(candidates)
        
        # Identify concept types
        concept_types = self._identify_concepts(candidates, token_pos)
        
        return SemanticCandidates(
            token_id=token_id,
            form=surface,
            candidates=candidates,
            denotation_types=denotation_types,
            concept_types=concept_types,
        )
    
    def _lookup_lexicon(
        self, 
        surface: str, 
        morphology: Dict[str, Any],
        pos: Dict[str, str]
    ) -> List[Dict[str, Any]]:
        """
        Look up possible meanings in lexicon
        
        Returns multiple candidates with metadata.
        """
        # Simplified lexicon lookup
        # In production, query FractalHub dictionary or corpus
        
        candidates = []
        
        # Example entries for common words
        lexicon_examples = {
            "كتب": [
                {"meaning": "wrote", "root": "كتب", "sense": "action_of_writing"},
                {"meaning": "books", "root": "كتب", "sense": "written_objects"},
            ],
            "في": [
                {"meaning": "in", "sense": "containment"},
                {"meaning": "at", "sense": "location"},
            ],
        }
        
        # Look up surface form
        if surface in lexicon_examples:
            candidates = lexicon_examples[surface]
        else:
            # Generate generic candidate
            candidates = [{
                "meaning": f"meaning_of_{surface}",
                "root": morphology.get("root", "unknown"),
                "sense": "unspecified",
            }]
        
        # Add metadata
        for candidate in candidates:
            candidate["token_id"] = morphology.get("token_id", "unknown")
            candidate["pos"] = pos.get("pos", "unknown")
            candidate["confidence"] = 0.5  # Would be computed from corpus frequency
        
        return candidates
    
    def _classify_denotation(self, candidates: List[Dict[str, Any]]) -> Dict[str, List[str]]:
        """
        Classify candidates by denotation type
        
        Types:
        - Mutabaqa (المطابقة): Full meaning
        - Tadammun (التضمن): Partial meaning
        - Iltizam (الالتزام): Necessary implication
        """
        denotation = {
            "mutabaqa": [],  # Full/primary meanings
            "tadammun": [],  # Partial meanings
            "iltizam": [],  # Implied meanings
        }
        
        for candidate in candidates:
            sense = candidate.get("sense", "unspecified")
            
            # Classify based on sense metadata
            # Primary meanings
            if "action" in sense or "object" in sense:
                denotation["mutabaqa"].append(candidate["meaning"])
            
            # Partial meanings (parts of the whole)
            if "part" in sense or "aspect" in sense:
                denotation["tadammun"].append(candidate["meaning"])
            
            # Implied meanings
            if "implication" in sense or sense == "unspecified":
                denotation["iltizam"].append(candidate["meaning"])
        
        return denotation
    
    def _identify_concepts(
        self, 
        candidates: List[Dict[str, Any]],
        pos: Dict[str, str]
    ) -> List[str]:
        """
        Identify concept types
        
        Types:
        - Entity: Objects, persons, places
        - Event: Actions, processes
        - Relation: Connections between entities
        - Modality: Possibility, necessity
        - Value: Properties, qualities
        """
        concept_types = set()
        
        # Based on POS
        pos_tag = pos.get("pos", "unknown")
        
        if pos_tag == "noun":
            concept_types.add("entity")
        elif pos_tag == "verb":
            concept_types.add("event")
        elif pos_tag == "particle":
            concept_types.add("relation")
        
        # Based on candidate meanings
        for candidate in candidates:
            meaning = candidate.get("meaning", "")
            
            if any(word in meaning for word in ["can", "must", "should", "يجب", "يمكن"]):
                concept_types.add("modality")
            
            if any(word in meaning for word in ["good", "bad", "big", "small", "جيد", "كبير"]):
                concept_types.add("value")
        
        return list(concept_types)
