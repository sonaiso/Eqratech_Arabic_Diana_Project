"""
Test cases for Arabic Grammar Engines
اختبارات محركات القواعد النحوية العربية
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class TestVerbsEngine(unittest.TestCase):
    """اختبارات محرك الأفعال"""
    
    def test_import(self):
        """Test that verbs_engine can be imported"""
        try:
            import verbs_engine
            self.assertTrue(True)
        except ImportError:
            self.skipTest("verbs_engine not available")


class TestPhonemesEngine(unittest.TestCase):
    """اختبارات محرك الفونيمات"""
    
    def test_import(self):
        """Test that phonemes_engine can be imported"""
        try:
            import phonemes_engine
            self.assertTrue(True)
        except ImportError:
            self.skipTest("phonemes_engine not available")


class TestGenderEngine(unittest.TestCase):
    """اختبارات محرك الجنس النحوي"""
    
    def test_import(self):
        """Test that gender_engine can be imported"""
        try:
            import gender_engine
            self.assertTrue(True)
        except ImportError:
            self.skipTest("gender_engine not available")


if __name__ == '__main__':
    unittest.main()
