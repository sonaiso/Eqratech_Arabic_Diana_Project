"""
FractalHub FormCodec

100% reversible encoding: text ⇄ numbers with checksum.
Maintains strict separation between signifier (C1) and signified (C3).

Core principle: Form must be perfectly preserved and recoverable.
"""

from typing import List, Tuple, Optional
import hashlib


class FormCodec:
    """
    100% reversible text to number encoding with checksum validation.
    
    Ensures perfect preservation of form (signifier layer).
    No meaning - only form transformation.
    
    Example:
        >>> codec = FormCodec()
        >>> encoded = codec.encode("السلام")
        >>> decoded = codec.decode(encoded)
        >>> decoded == "السلام"
        True
    """
    
    def __init__(self):
        """Initialize codec."""
        self.encoding = 'utf-8'
    
    def encode(self, text: str) -> Tuple[List[int], str]:
        """
        Encode text to list of numbers with checksum.
        
        Args:
            text: Input text (signifier form)
            
        Returns:
            (encoded_numbers, checksum)
            
        Example:
            >>> codec = FormCodec()
            >>> numbers, checksum = codec.encode("مرحبا")
            >>> isinstance(numbers, list)
            True
            >>> isinstance(checksum, str)
            True
        """
        if not isinstance(text, str):
            raise TypeError(f"Input must be string, got {type(text)}")
        
        # Convert to bytes then to list of integers
        bytes_data = text.encode(self.encoding)
        encoded = list(bytes_data)
        
        # Generate checksum for verification
        checksum = self._generate_checksum(encoded)
        
        return (encoded, checksum)
    
    def decode(self, encoded: List[int], checksum: Optional[str] = None) -> str:
        """
        Decode list of numbers back to text with optional checksum verification.
        
        Args:
            encoded: List of encoded integers
            checksum: Optional checksum for verification
            
        Returns:
            Decoded text
            
        Raises:
            ValueError: If checksum verification fails
            
        Example:
            >>> codec = FormCodec()
            >>> numbers, cs = codec.encode("مرحبا")
            >>> decoded = codec.decode(numbers, cs)
            >>> decoded == "مرحبا"
            True
        """
        if not isinstance(encoded, list):
            raise TypeError(f"Encoded must be list, got {type(encoded)}")
        
        # Verify checksum if provided
        if checksum is not None:
            computed_checksum = self._generate_checksum(encoded)
            if computed_checksum != checksum:
                raise ValueError(
                    f"Checksum verification failed. "
                    f"Expected: {checksum}, Got: {computed_checksum}"
                )
        
        # Convert integers back to bytes then to string
        bytes_data = bytes(encoded)
        decoded = bytes_data.decode(self.encoding)
        
        return decoded
    
    def _generate_checksum(self, encoded: List[int]) -> str:
        """
        Generate SHA-256 checksum for encoded data.
        
        Args:
            encoded: List of encoded integers
            
        Returns:
            Hexadecimal checksum string
        """
        # Convert to bytes and hash
        bytes_data = bytes(encoded)
        hash_obj = hashlib.sha256(bytes_data)
        return hash_obj.hexdigest()
    
    def verify_reversibility(self, text: str) -> bool:
        """
        Test that encoding and decoding are perfectly reversible.
        
        Args:
            text: Text to test
            
        Returns:
            True if reversible, False otherwise
            
        Example:
            >>> codec = FormCodec()
            >>> codec.verify_reversibility("اختبار النص العربي")
            True
        """
        try:
            encoded, checksum = self.encode(text)
            decoded = self.decode(encoded, checksum)
            return text == decoded
        except Exception:
            return False
    
    def batch_encode(self, texts: List[str]) -> List[Tuple[List[int], str]]:
        """
        Encode multiple texts.
        
        Args:
            texts: List of texts to encode
            
        Returns:
            List of (encoded, checksum) tuples
        """
        return [self.encode(text) for text in texts]
    
    def batch_decode(self, encoded_data: List[Tuple[List[int], str]]) -> List[str]:
        """
        Decode multiple encoded texts.
        
        Args:
            encoded_data: List of (encoded, checksum) tuples
            
        Returns:
            List of decoded texts
        """
        return [self.decode(enc, cs) for enc, cs in encoded_data]
    
    def get_encoding_stats(self, text: str) -> dict:
        """
        Get statistics about encoded text.
        
        Args:
            text: Text to analyze
            
        Returns:
            Dictionary with encoding statistics
        """
        encoded, checksum = self.encode(text)
        
        return {
            "original_length": len(text),
            "encoded_length": len(encoded),
            "checksum": checksum,
            "compression_ratio": len(encoded) / len(text) if len(text) > 0 else 0,
            "encoding": self.encoding,
        }


class MeaningCodec:
    """
    Enhanced codec for meaning (C3 layer) with provenance tracking.
    
    Unlike FormCodec (which handles signifiers), MeaningCodec handles
    signified content with full trace preservation.
    
    Core principle: NO meaning without C2 trace.
    """
    
    def __init__(self):
        """Initialize meaning codec."""
        pass
    
    def encode_meaning(
        self,
        concept: str,
        trace_id: str,
        prior_ids: dict,
        provenance: List[dict]
    ) -> dict:
        """
        Encode meaning with full provenance.
        
        Args:
            concept: The meaning/concept
            trace_id: Required C2 trace
            prior_ids: Dictionary evidence
            provenance: Source information
            
        Returns:
            Encoded meaning object
            
        Raises:
            ValueError: If trace_id or prior_ids missing
        """
        if not trace_id:
            raise ValueError("NO meaning without C2 trace")
        
        if not prior_ids or not any(prior_ids.values()):
            raise ValueError("NO meaning without prior_ids evidence")
        
        return {
            "concept": concept,
            "trace_id": trace_id,
            "prior_ids": prior_ids,
            "provenance": provenance,
            "layer": "C3",
        }
    
    def decode_meaning(self, encoded_meaning: dict) -> Tuple[str, str, dict]:
        """
        Decode meaning with validation.
        
        Args:
            encoded_meaning: Encoded meaning object
            
        Returns:
            (concept, trace_id, prior_ids)
            
        Raises:
            ValueError: If required fields missing
        """
        if "trace_id" not in encoded_meaning:
            raise ValueError("Cannot decode meaning without trace_id")
        
        if "prior_ids" not in encoded_meaning:
            raise ValueError("Cannot decode meaning without prior_ids")
        
        return (
            encoded_meaning["concept"],
            encoded_meaning["trace_id"],
            encoded_meaning["prior_ids"]
        )
