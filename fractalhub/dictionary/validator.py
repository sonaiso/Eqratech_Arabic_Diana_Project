"""
FractalHub Dictionary Validator

Validates dictionary structure, provenance, and integrity.
Ensures compliance with v02 schema requirements.
"""

import yaml
from pathlib import Path
from typing import Dict, List, Any, Set, Tuple


class DictionaryValidator:
    """
    Validates FractalHub Dictionary v02 structure and content.
    
    Checks:
    - Schema compliance
    - Provenance completeness
    - Entry type separation (signifier vs signified)
    - Ruleset validity
    - DRY principle (no duplicates)
    - Cross-references integrity
    """
    
    def __init__(self, dictionary_path: str):
        """
        Initialize validator.
        
        Args:
            dictionary_path: Path to dictionary YAML file
        """
        self.dictionary_path = Path(dictionary_path)
        self.data: Dict[str, Any] = {}
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self._load()
    
    def _load(self) -> None:
        """Load dictionary from YAML file."""
        if not self.dictionary_path.exists():
            raise FileNotFoundError(f"Dictionary not found: {self.dictionary_path}")
        
        with open(self.dictionary_path, 'r', encoding='utf-8') as f:
            self.data = yaml.safe_load(f)
        
        if not self.data:
            raise ValueError(f"Empty dictionary: {self.dictionary_path}")
    
    def validate(self) -> Tuple[bool, List[str], List[str]]:
        """
        Run all validation checks.
        
        Returns:
            (is_valid, errors, warnings)
        """
        self.errors = []
        self.warnings = []
        
        # Run validation checks
        self._validate_meta()
        self._validate_provenance()
        self._validate_lexicon()
        self._validate_rulesets()
        self._validate_gates()
        self._validate_evidence()
        self._validate_invariants()
        self._validate_mappings()
        self._validate_cross_references()
        self._check_dry_principle()
        
        return (len(self.errors) == 0, self.errors, self.warnings)
    
    def _validate_meta(self) -> None:
        """Validate metadata section."""
        if 'meta' not in self.data:
            self.errors.append("Missing 'meta' section")
            return
        
        meta = self.data['meta']
        required_fields = [
            'dict_version', 'codec_version', 'schema_version',
            'generated_at', 'compatibility', 'changelog'
        ]
        
        for field in required_fields:
            if field not in meta:
                self.errors.append(f"Meta missing required field: {field}")
        
        # Check version
        if meta.get('dict_version') != 2:
            self.errors.append(f"Expected dict_version 2, got {meta.get('dict_version')}")
        
        # Check compatibility
        if 'compatibility' in meta:
            comp = meta['compatibility']
            if 'v01_supported' not in comp:
                self.warnings.append("Compatibility: v01_supported not specified")
            if 'breaking_changes' not in comp:
                self.warnings.append("Compatibility: breaking_changes not specified")
    
    def _validate_provenance(self) -> None:
        """Validate provenance section."""
        if 'provenance' not in self.data:
            self.errors.append("Missing 'provenance' section")
            return
        
        if 'sources' not in self.data['provenance']:
            self.errors.append("Provenance missing 'sources'")
            return
        
        sources = self.data['provenance']['sources']
        
        # Check each source
        for source_id, source in sources.items():
            required = ['source_id', 'type', 'description_ar', 'description_en', 'reliability']
            for field in required:
                if field not in source:
                    self.errors.append(f"Source {source_id} missing field: {field}")
            
            # Validate reliability
            if 'reliability' in source:
                rel = source['reliability']
                if not isinstance(rel, (int, float)) or not (0.0 <= rel <= 1.0):
                    self.errors.append(
                        f"Source {source_id} reliability must be 0.0-1.0, got {rel}"
                    )
    
    def _validate_lexicon(self) -> None:
        """Validate lexicon entries."""
        if 'lexicon' not in self.data:
            self.errors.append("Missing 'lexicon' section")
            return
        
        lexicon = self.data['lexicon']
        signifier_count = 0
        signified_count = 0
        
        for entry_id, entry in lexicon.items():
            # Check entry_id matches
            if entry.get('entry_id') != entry_id:
                self.errors.append(
                    f"Entry ID mismatch: key={entry_id}, value={entry.get('entry_id')}"
                )
            
            # Check entry_type
            entry_type = entry.get('entry_type')
            if entry_type not in ['signifier', 'signified']:
                self.errors.append(
                    f"Entry {entry_id} has invalid entry_type: {entry_type}"
                )
            
            # Count types
            if entry_type == 'signifier':
                signifier_count += 1
                self._validate_signifier_entry(entry_id, entry)
            elif entry_type == 'signified':
                signified_count += 1
                self._validate_signified_entry(entry_id, entry)
            
            # Check provenance
            if 'provenance' not in entry:
                self.warnings.append(f"Entry {entry_id} missing provenance")
            else:
                self._validate_entry_provenance(entry_id, entry['provenance'])
            
            # Check status
            if 'status' not in entry:
                self.warnings.append(f"Entry {entry_id} missing status")
        
        # Report counts
        if signifier_count == 0:
            self.warnings.append("No signifier entries found")
        if signified_count == 0:
            self.warnings.append("No signified entries found")
    
    def _validate_signifier_entry(self, entry_id: str, entry: Dict[str, Any]) -> None:
        """Validate signifier (C1) entry."""
        required = ['layer', 'form', 'form_ar', 'form_en', 'features']
        for field in required:
            if field not in entry:
                self.errors.append(f"Signifier {entry_id} missing field: {field}")
        
        # Check layer
        if entry.get('layer') != 'C1':
            self.errors.append(f"Signifier {entry_id} must have layer=C1")
        
        # Signifiers should NOT have semantic features or meaning
        forbidden = ['semantic_features', 'concept_ar', 'concept_en']
        for field in forbidden:
            if field in entry:
                self.errors.append(
                    f"Signifier {entry_id} must not have {field} (C1 is form only)"
                )
    
    def _validate_signified_entry(self, entry_id: str, entry: Dict[str, Any]) -> None:
        """Validate signified (C3) entry."""
        required = ['layer', 'concept_ar', 'concept_en', 'semantic_features', 'ontology_type']
        for field in required:
            if field not in entry:
                self.errors.append(f"Signified {entry_id} missing field: {field}")
        
        # Check layer
        if entry.get('layer') != 'C3':
            self.errors.append(f"Signified {entry_id} must have layer=C3")
        
        # Check linked signifiers
        if 'linked_signifiers' not in entry:
            self.warnings.append(f"Signified {entry_id} has no linked_signifiers")
    
    def _validate_entry_provenance(self, entry_id: str, provenance: List[Dict]) -> None:
        """Validate entry provenance."""
        if not isinstance(provenance, list):
            self.errors.append(f"Entry {entry_id} provenance must be a list")
            return
        
        for prov in provenance:
            if 'source_id' not in prov:
                self.errors.append(f"Entry {entry_id} provenance missing source_id")
            if 'confidence' not in prov:
                self.errors.append(f"Entry {entry_id} provenance missing confidence")
            
            # Check if source exists
            if 'source_id' in prov:
                source_id = prov['source_id']
                sources = self.data.get('provenance', {}).get('sources', {})
                if source_id not in sources:
                    self.errors.append(
                        f"Entry {entry_id} references unknown source: {source_id}"
                    )
    
    def _validate_rulesets(self) -> None:
        """Validate rulesets."""
        if 'rulesets' not in self.data:
            self.warnings.append("Missing 'rulesets' section")
            return
        
        rulesets = self.data['rulesets']
        
        for ruleset_id, ruleset in rulesets.items():
            # Check ID match
            if ruleset.get('ruleset_id') != ruleset_id:
                self.errors.append(
                    f"Ruleset ID mismatch: key={ruleset_id}, value={ruleset.get('ruleset_id')}"
                )
            
            # Check required fields
            required = ['type', 'description_ar', 'description_en', 'layer', 'provenance']
            for field in required:
                if field not in ruleset:
                    self.errors.append(f"Ruleset {ruleset_id} missing field: {field}")
            
            # Check layer
            layer = ruleset.get('layer')
            if layer not in ['C0', 'C1', 'C2', 'C3']:
                self.errors.append(f"Ruleset {ruleset_id} has invalid layer: {layer}")
    
    def _validate_gates(self) -> None:
        """Validate gates."""
        if 'gates' not in self.data:
            self.warnings.append("Missing 'gates' section")
            return
        
        gates = self.data['gates']
        expected_gates = ['G_ATTEND', 'G_CODEC_VERIFY', 'G_SPEECH_ACT', 'G_MEMORY_READ', 'G_MEMORY_WRITE']
        
        for gate_id in expected_gates:
            if gate_id not in gates:
                self.warnings.append(f"Expected gate not found: {gate_id}")
        
        for gate_id, gate in gates.items():
            required = ['gate_type', 'description_ar', 'description_en', 'layer', 'function']
            for field in required:
                if field not in gate:
                    self.errors.append(f"Gate {gate_id} missing field: {field}")
            
            # Check layer
            if gate.get('layer') != 'C2':
                self.errors.append(f"Gate {gate_id} must have layer=C2")
            
            # Check requires_four_conditions
            if not gate.get('requires_four_conditions'):
                self.warnings.append(
                    f"Gate {gate_id} should require four conditions"
                )
    
    def _validate_evidence(self) -> None:
        """Validate evidence section."""
        if 'evidence' not in self.data:
            self.warnings.append("Missing 'evidence' section")
            return
        
        evidence = self.data['evidence']
        
        # Check epistemic_strength
        if 'epistemic_strength' in evidence:
            expected = ['YAQIN', 'ZANN', 'SHAKK']
            for level in expected:
                if level not in evidence['epistemic_strength']:
                    self.warnings.append(f"Missing epistemic strength level: {level}")
        
        # Check reasoning_modes
        if 'reasoning_modes' in evidence:
            expected = ['DEDUCTIVE', 'INDUCTIVE', 'ABDUCTIVE', 'INFERENTIAL']
            for mode in expected:
                if mode not in evidence['reasoning_modes']:
                    self.warnings.append(f"Missing reasoning mode: {mode}")
    
    def _validate_invariants(self) -> None:
        """Validate invariants section."""
        if 'invariants' not in self.data:
            self.warnings.append("Missing 'invariants' section")
            return
        
        invariants = self.data['invariants']
        
        # Check conservation laws
        if 'conservation_laws' in invariants:
            expected = ['TEMPORAL', 'REFERENTIAL', 'CAUSAL', 'PREDICATIVE', 'QUANTITATIVE', 'SCOPE']
            for law in expected:
                if law not in invariants['conservation_laws']:
                    self.warnings.append(f"Missing conservation law: {law}")
        
        # Check symmetry rules
        if 'symmetry_rules' in invariants:
            expected = ['LOGICAL', 'STRUCTURAL', 'SEMANTIC', 'PRAGMATIC']
            for rule in expected:
                if rule not in invariants['symmetry_rules']:
                    self.warnings.append(f"Missing symmetry rule: {rule}")
    
    def _validate_mappings(self) -> None:
        """Validate mappings section."""
        if 'mappings' not in self.data:
            self.warnings.append("Missing 'mappings' section")
            return
        
        mappings = self.data['mappings']
        
        # Check signifier_to_signified
        if 'signifier_to_signified' in mappings:
            s2s = mappings['signifier_to_signified']
            lexicon = self.data.get('lexicon', {})
            
            for key, mapping in s2s.items():
                # Check signifier exists
                if 'signifier' in mapping:
                    sig_id = mapping['signifier']
                    if sig_id not in lexicon:
                        self.errors.append(
                            f"Mapping {key} references unknown signifier: {sig_id}"
                        )
                
                # Check signifieds exist
                if 'signifieds' in mapping:
                    for sig_id in mapping['signifieds']:
                        if sig_id not in lexicon:
                            self.errors.append(
                                f"Mapping {key} references unknown signified: {sig_id}"
                            )
    
    def _validate_cross_references(self) -> None:
        """Validate cross-references between sections."""
        lexicon = self.data.get('lexicon', {})
        rulesets = self.data.get('rulesets', {})
        
        # Check linked_signifiers in signified entries
        for entry_id, entry in lexicon.items():
            if entry.get('entry_type') == 'signified':
                if 'linked_signifiers' in entry:
                    for sig_id in entry['linked_signifiers']:
                        if sig_id not in lexicon:
                            self.errors.append(
                                f"Signified {entry_id} references unknown signifier: {sig_id}"
                            )
                        elif lexicon[sig_id].get('entry_type') != 'signifier':
                            self.errors.append(
                                f"Signified {entry_id} linked_signifiers contains non-signifier: {sig_id}"
                            )
    
    def _check_dry_principle(self) -> None:
        """Check for duplicate content (DRY principle)."""
        lexicon = self.data.get('lexicon', {})
        
        # Check for duplicate forms
        forms: Dict[str, List[str]] = {}
        for entry_id, entry in lexicon.items():
            if entry.get('entry_type') == 'signifier':
                form = entry.get('form')
                if form:
                    if form not in forms:
                        forms[form] = []
                    forms[form].append(entry_id)
        
        for form, entry_ids in forms.items():
            if len(entry_ids) > 1:
                self.warnings.append(
                    f"Duplicate form '{form}' in entries: {', '.join(entry_ids)}"
                )
    
    def get_report(self) -> str:
        """
        Get validation report.
        
        Returns:
            Formatted validation report
        """
        report = []
        report.append("=" * 70)
        report.append("FractalHub Dictionary v02 Validation Report")
        report.append("=" * 70)
        report.append(f"Dictionary: {self.dictionary_path}")
        report.append("")
        
        # Summary
        if len(self.errors) == 0 and len(self.warnings) == 0:
            report.append("✅ PASSED - No errors or warnings")
        elif len(self.errors) == 0:
            report.append(f"⚠️  PASSED WITH WARNINGS - {len(self.warnings)} warning(s)")
        else:
            report.append(f"❌ FAILED - {len(self.errors)} error(s), {len(self.warnings)} warning(s)")
        
        report.append("")
        
        # Errors
        if self.errors:
            report.append(f"Errors ({len(self.errors)}):")
            for i, error in enumerate(self.errors, 1):
                report.append(f"  {i}. {error}")
            report.append("")
        
        # Warnings
        if self.warnings:
            report.append(f"Warnings ({len(self.warnings)}):")
            for i, warning in enumerate(self.warnings, 1):
                report.append(f"  {i}. {warning}")
            report.append("")
        
        report.append("=" * 70)
        return "\n".join(report)
