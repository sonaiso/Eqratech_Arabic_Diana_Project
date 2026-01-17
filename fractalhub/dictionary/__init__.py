"""
FractalHub Dictionary Module

Loads and provides access to the FractalHub Dictionary v02.
Supports bilingual entries with full provenance tracking.
"""

import yaml
from pathlib import Path
from typing import Dict, List, Optional, Any


class DictionaryLoader:
    """
    Loads and provides access to FractalHub Dictionary v02.
    
    Example:
        >>> loader = DictionaryLoader()
        >>> entry = loader.get_lexicon_entry("SIGNIFIER:FATHA")
        >>> entry['form']
        'َ'
    """
    
    def __init__(self, dictionary_path: Optional[str] = None):
        """
        Initialize dictionary loader.
        
        Args:
            dictionary_path: Path to dictionary YAML file.
                           If None, uses default v02 dictionary.
        """
        if dictionary_path is None:
            # Default to v02 dictionary
            module_dir = Path(__file__).parent.parent
            dictionary_path = module_dir / "data" / "fractalhub_dictionary_v02.yaml"
        
        self.dictionary_path = Path(dictionary_path)
        self.data: Dict[str, Any] = {}
        self._load()
    
    def _load(self) -> None:
        """Load dictionary from YAML file."""
        if not self.dictionary_path.exists():
            raise FileNotFoundError(f"Dictionary not found: {self.dictionary_path}")
        
        with open(self.dictionary_path, 'r', encoding='utf-8') as f:
            self.data = yaml.safe_load(f)
        
        if not self.data:
            raise ValueError(f"Empty dictionary: {self.dictionary_path}")
    
    def get_meta(self) -> Dict[str, Any]:
        """Get dictionary metadata."""
        return self.data.get('meta', {})
    
    def get_version(self) -> int:
        """Get dictionary version."""
        return self.get_meta().get('dict_version', 0)
    
    def get_provenance_sources(self) -> Dict[str, Any]:
        """Get all provenance sources."""
        return self.data.get('provenance', {}).get('sources', {})
    
    def get_provenance_source(self, source_id: str) -> Optional[Dict[str, Any]]:
        """
        Get specific provenance source.
        
        Args:
            source_id: Source identifier (e.g., "CLASSICAL_CORPUS")
            
        Returns:
            Source information or None if not found
        """
        return self.get_provenance_sources().get(source_id)
    
    def get_lexicon(self) -> Dict[str, Any]:
        """Get entire lexicon."""
        return self.data.get('lexicon', {})
    
    def get_lexicon_entry(self, entry_id: str) -> Optional[Dict[str, Any]]:
        """
        Get specific lexicon entry.
        
        Args:
            entry_id: Entry identifier (e.g., "SIGNIFIER:FATHA")
            
        Returns:
            Entry data or None if not found
        """
        return self.get_lexicon().get(entry_id)
    
    def get_signifier_entries(self) -> Dict[str, Any]:
        """Get all signifier (C1) entries."""
        return {
            k: v for k, v in self.get_lexicon().items()
            if v.get('entry_type') == 'signifier'
        }
    
    def get_signified_entries(self) -> Dict[str, Any]:
        """Get all signified (C3) entries."""
        return {
            k: v for k, v in self.get_lexicon().items()
            if v.get('entry_type') == 'signified'
        }
    
    def get_rulesets(self) -> Dict[str, Any]:
        """Get all rulesets."""
        return self.data.get('rulesets', {})
    
    def get_ruleset(self, ruleset_id: str) -> Optional[Dict[str, Any]]:
        """
        Get specific ruleset.
        
        Args:
            ruleset_id: Ruleset identifier (e.g., "PHONOLOGY:DOUBLE_SUKUN")
            
        Returns:
            Ruleset data or None if not found
        """
        return self.get_rulesets().get(ruleset_id)
    
    def get_rulesets_by_layer(self, layer: str) -> Dict[str, Any]:
        """
        Get rulesets for specific layer.
        
        Args:
            layer: Layer identifier ("C0", "C1", "C2", "C3")
            
        Returns:
            Dictionary of rulesets for that layer
        """
        return {
            k: v for k, v in self.get_rulesets().items()
            if v.get('layer') == layer
        }
    
    def get_gates(self) -> Dict[str, Any]:
        """Get all gates."""
        return self.data.get('gates', {})
    
    def get_gate(self, gate_id: str) -> Optional[Dict[str, Any]]:
        """
        Get specific gate.
        
        Args:
            gate_id: Gate identifier (e.g., "G_ATTEND")
            
        Returns:
            Gate data or None if not found
        """
        return self.get_gates().get(gate_id)
    
    def get_evidence_config(self) -> Dict[str, Any]:
        """Get evidence configuration."""
        return self.data.get('evidence', {})
    
    def get_epistemic_strengths(self) -> Dict[str, Any]:
        """Get epistemic strength definitions."""
        return self.get_evidence_config().get('epistemic_strength', {})
    
    def get_reasoning_modes(self) -> Dict[str, Any]:
        """Get reasoning mode definitions."""
        return self.get_evidence_config().get('reasoning_modes', {})
    
    def get_invariants(self) -> Dict[str, Any]:
        """Get all invariants."""
        return self.data.get('invariants', {})
    
    def get_conservation_laws(self) -> Dict[str, Any]:
        """Get conservation laws."""
        return self.get_invariants().get('conservation_laws', {})
    
    def get_symmetry_rules(self) -> Dict[str, Any]:
        """Get symmetry rules."""
        return self.get_invariants().get('symmetry_rules', {})
    
    def get_mappings(self) -> Dict[str, Any]:
        """Get all mappings."""
        return self.data.get('mappings', {})
    
    def get_signifier_to_signified_mapping(self, key: str) -> Optional[Dict[str, Any]]:
        """
        Get signifier to signified mapping.
        
        Args:
            key: Mapping key (e.g., "KITAB")
            
        Returns:
            Mapping data or None if not found
        """
        mappings = self.get_mappings().get('signifier_to_signified', {})
        return mappings.get(key)
    
    def search_by_form(self, form: str) -> List[Dict[str, Any]]:
        """
        Search lexicon entries by form.
        
        Args:
            form: Form to search for (e.g., "كتاب")
            
        Returns:
            List of matching entries
        """
        results = []
        for entry_id, entry in self.get_lexicon().items():
            if entry.get('form') == form or entry.get('concept_ar') == form:
                results.append({'entry_id': entry_id, **entry})
        return results
    
    def validate_prior_ids(self, prior_ids: Dict[str, List[str]]) -> tuple[bool, List[str]]:
        """
        Validate that prior_ids reference existing entries.
        
        Args:
            prior_ids: Dictionary of prior IDs to validate
                      {'lexicon_ids': [...], 'ruleset_ids': [...]}
        
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        # Validate lexicon_ids
        if 'lexicon_ids' in prior_ids:
            for lex_id in prior_ids['lexicon_ids']:
                if not self.get_lexicon_entry(lex_id):
                    errors.append(f"Lexicon entry not found: {lex_id}")
        
        # Validate ruleset_ids
        if 'ruleset_ids' in prior_ids:
            for rule_id in prior_ids['ruleset_ids']:
                if not self.get_ruleset(rule_id):
                    errors.append(f"Ruleset not found: {rule_id}")
        
        return (len(errors) == 0, errors)


# Global dictionary loader instance
_dictionary_loader: Optional[DictionaryLoader] = None


def get_dictionary() -> DictionaryLoader:
    """
    Get global dictionary loader instance.
    
    Returns:
        Global DictionaryLoader instance
    """
    global _dictionary_loader
    if _dictionary_loader is None:
        _dictionary_loader = DictionaryLoader()
    return _dictionary_loader


def reload_dictionary(dictionary_path: Optional[str] = None) -> DictionaryLoader:
    """
    Reload dictionary with optional custom path.
    
    Args:
        dictionary_path: Optional path to dictionary file
        
    Returns:
        New DictionaryLoader instance
    """
    global _dictionary_loader
    _dictionary_loader = DictionaryLoader(dictionary_path)
    return _dictionary_loader
