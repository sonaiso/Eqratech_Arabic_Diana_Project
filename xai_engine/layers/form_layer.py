"""
Form Layer (الدال) - Layer 1

Purpose: Build the FORM structure without any meaning
Output: ParseTree

This layer:
- Tokenizes the input
- Analyzes phonology (consonants/vowels)
- Analyzes morphology (roots/patterns)
- Assigns POS tags
- Detects built vs inflected forms

NO MEANING. NO JUDGMENT. Pure form analysis.
"""

from typing import Any, Dict, List
import re
from .base import LayerBase
from ..core.output_objects import ParseTree
from ..core.domain import Domain


class FormLayer(LayerBase):
    """
    Layer 1: Form analysis
    
    Converts raw input text into structured form representation.
    """
    
    def __init__(self, domain: Domain):
        super().__init__("form", domain)
    
    def process(self, input_data: str) -> ParseTree:
        """
        Process raw text input and produce form structure
        
        Args:
            input_data: Raw text string
            
        Returns:
            ParseTree with form analysis
        """
        self.log_operation("start_form_analysis", {"input_length": len(input_data)})
        
        # Tokenization
        tokens = self._tokenize(input_data)
        self.log_operation("tokenization", {"token_count": len(tokens)})
        
        # Phonological analysis
        phonology = self._analyze_phonology(tokens)
        self.log_operation("phonology_analysis", {"phoneme_count": len(phonology.get("phonemes", []))})
        
        # Morphological analysis
        morphology = self._analyze_morphology(tokens)
        self.log_operation("morphology_analysis", {"analyzed_tokens": len(morphology.get("forms", []))})
        
        # POS tagging
        pos_tags = self._assign_pos_tags(tokens, morphology)
        self.log_operation("pos_tagging", {"tagged_count": len(pos_tags)})
        
        # Build parse tree
        tree = self._build_tree(tokens, pos_tags)
        self.log_operation("tree_building", {"tree_depth": tree.get("depth", 0)})
        
        return ParseTree(
            text=input_data,
            tokens=tokens,
            tree=tree,
            phonology=phonology,
            morphology=morphology,
            pos_tags=pos_tags,
        )
    
    def _tokenize(self, text: str) -> List[Dict[str, Any]]:
        """
        Tokenize text into units
        
        For Arabic: split on whitespace and preserve diacritics
        For other domains: use appropriate tokenization
        """
        # Simple whitespace tokenization with token IDs
        words = text.strip().split()
        
        tokens = []
        for idx, word in enumerate(words):
            tokens.append({
                "token_id": f"T{idx:03d}",
                "surface": word,
                "position": idx,
                "length": len(word),
            })
        
        return tokens
    
    def _analyze_phonology(self, tokens: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Analyze phonological structure
        
        Identifies:
        - Consonants (صوامت)
        - Vowels (صوائت)
        - Diacritics (حركات)
        - Stress patterns
        """
        phonemes = []
        
        # Arabic phonological categories
        arabic_consonants = set("بتثجحخدذرزسشصضطظعغفقكلمنهوي")
        arabic_vowels = set("اآأإةى")
        diacritics = set("\u064B\u064C\u064D\u064E\u064F\u0650\u0651\u0652")  # Fatha, Damma, Kasra, etc.
        
        for token in tokens:
            surface = token["surface"]
            token_phonemes = {
                "token_id": token["token_id"],
                "consonants": [],
                "vowels": [],
                "diacritics": [],
            }
            
            for char in surface:
                if char in arabic_consonants:
                    token_phonemes["consonants"].append(char)
                elif char in arabic_vowels:
                    token_phonemes["vowels"].append(char)
                elif char in diacritics:
                    token_phonemes["diacritics"].append(char)
            
            phonemes.append(token_phonemes)
        
        return {
            "phonemes": phonemes,
            "total_consonants": sum(len(p["consonants"]) for p in phonemes),
            "total_vowels": sum(len(p["vowels"]) for p in phonemes),
            "total_diacritics": sum(len(p["diacritics"]) for p in phonemes),
        }
    
    def _analyze_morphology(self, tokens: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Analyze morphological structure
        
        Identifies:
        - Root (جذر)
        - Pattern (وزن)
        - Affixes (سوابق/لواحق)
        """
        forms = []
        
        for token in tokens:
            surface = token["surface"]
            
            # Simplified morphological analysis
            # In production, use actual morphological analyzer
            form_analysis = {
                "token_id": token["token_id"],
                "surface": surface,
                "root": self._extract_root(surface),
                "pattern": self._detect_pattern(surface),
                "prefixes": self._extract_prefixes(surface),
                "suffixes": self._extract_suffixes(surface),
            }
            
            forms.append(form_analysis)
        
        return {
            "forms": forms,
            "analyzed_count": len(forms),
        }
    
    def _extract_root(self, surface: str) -> str:
        """Extract root (simplified)"""
        # Remove common prefixes/suffixes and diacritics
        cleaned = surface
        for dia in ["\u064B", "\u064C", "\u064D", "\u064E", "\u064F", "\u0650", "\u0651", "\u0652"]:
            cleaned = cleaned.replace(dia, "")
        
        # Very simplified - just take core letters (3-4 consonants)
        consonants = "".join(c for c in cleaned if c in "بتثجحخدذرزسشصضطظعغفقكلمنهوي")
        return consonants[:4] if len(consonants) >= 3 else consonants
    
    def _detect_pattern(self, surface: str) -> str:
        """Detect morphological pattern (simplified)"""
        # In production, use pattern matching against known patterns
        root_len = len(self._extract_root(surface))
        if root_len == 3:
            return "فَعَلَ"  # Default triliteral
        elif root_len == 4:
            return "فَعْلَلَ"  # Quadriliteral
        return "unknown"
    
    def _extract_prefixes(self, surface: str) -> List[str]:
        """Extract prefixes (simplified)"""
        prefixes = []
        # Common Arabic prefixes
        if surface.startswith("ال"):
            prefixes.append("ال")
        if surface.startswith("و"):
            prefixes.append("و")
        if surface.startswith("ف"):
            prefixes.append("ف")
        return prefixes
    
    def _extract_suffixes(self, surface: str) -> List[str]:
        """Extract suffixes (simplified)"""
        suffixes = []
        # Common Arabic suffixes
        if surface.endswith("ون"):
            suffixes.append("ون")
        elif surface.endswith("ين"):
            suffixes.append("ين")
        elif surface.endswith("ة"):
            suffixes.append("ة")
        return suffixes
    
    def _assign_pos_tags(self, tokens: List[Dict[str, Any]], morphology: Dict[str, Any]) -> List[Dict[str, str]]:
        """
        Assign Part-Of-Speech tags
        
        Categories:
        - اسم (noun)
        - فعل (verb)
        - حرف (particle)
        """
        pos_tags = []
        
        for token in tokens:
            # Simplified POS tagging based on morphology
            # In production, use statistical tagger
            surface = token["surface"]
            
            tag = "noun"  # Default
            
            # Simple heuristics
            if surface in ["في", "من", "إلى", "على", "عن"]:
                tag = "particle"
            elif surface.startswith("ي") or surface.startswith("ت") or surface.startswith("أ") or surface.startswith("ن"):
                # Starts with verb prefix
                tag = "verb"
            
            pos_tags.append({
                "token_id": token["token_id"],
                "surface": surface,
                "pos": tag,
            })
        
        return pos_tags
    
    def _build_tree(self, tokens: List[Dict[str, Any]], pos_tags: List[Dict[str, str]]) -> Dict[str, Any]:
        """
        Build syntactic tree structure (flat for now)
        
        In production, use dependency parser
        """
        nodes = []
        
        for token, pos in zip(tokens, pos_tags):
            nodes.append({
                "token_id": token["token_id"],
                "surface": token["surface"],
                "pos": pos["pos"],
                "parent": None,  # Would be set by parser
                "relation": None,  # Would be set by parser
            })
        
        return {
            "nodes": nodes,
            "edges": [],  # Would be populated by parser
            "depth": 1,  # Flat tree for now
            "root": nodes[0]["token_id"] if nodes else None,
        }
