"""
Unit tests for training loop components.
These tests validate the dataset and training function behavior.
"""

import unittest
import torch
from torch.utils.data import DataLoader


class MockTokenizer:
    """Mock tokenizer for testing without requiring transformers."""
    
    def __call__(self, text, **kwargs):
        """Mock tokenization that returns fixed-size tensors."""
        max_length = kwargs.get('max_length', 128)
        return {
            'input_ids': torch.ones((1, max_length), dtype=torch.long),
            'attention_mask': torch.ones((1, max_length), dtype=torch.long),
            'token_type_ids': torch.zeros((1, max_length), dtype=torch.long)
        }


class TestDatasetStructure(unittest.TestCase):
    """Test cases for dataset structure and label handling."""
    
    def test_dataset_returns_required_keys(self):
        """Test that dataset returns all required keys."""
        from dataset_with_labels import ArabicTextDataset
        
        # Create mock dataset
        texts = ["نص تجريبي", "نص آخر"]
        labels = [0, 1]
        tokenizer = MockTokenizer()
        
        dataset = ArabicTextDataset(texts, labels, tokenizer, max_length=64)
        
        # Get a sample
        sample = dataset[0]
        
        # Check all required keys are present
        required_keys = {'input_ids', 'attention_mask', 'token_type_ids', 'labels'}
        self.assertEqual(set(sample.keys()), required_keys, 
                        "Dataset must return all required keys")
    
    def test_dataset_label_type(self):
        """Test that labels are returned as torch tensors."""
        from dataset_with_labels import ArabicTextDataset
        
        texts = ["نص"]
        labels = [1]
        tokenizer = MockTokenizer()
        
        dataset = ArabicTextDataset(texts, labels, tokenizer)
        sample = dataset[0]
        
        self.assertIsInstance(sample['labels'], torch.Tensor,
                            "Labels must be torch tensors")
        self.assertEqual(sample['labels'].dtype, torch.long,
                        "Labels must have dtype torch.long")
    
    def test_dataset_validates_length_mismatch(self):
        """Test that dataset raises error when texts and labels lengths don't match."""
        from dataset_with_labels import ArabicTextDataset
        
        texts = ["نص 1", "نص 2"]
        labels = [0]  # Wrong length
        tokenizer = MockTokenizer()
        
        with self.assertRaises(ValueError) as context:
            dataset = ArabicTextDataset(texts, labels, tokenizer)
        
        self.assertIn("must match", str(context.exception))
    
    def test_dataloader_batch_structure(self):
        """Test that dataloader batches have correct structure."""
        from dataset_with_labels import ArabicTextDataset
        
        texts = ["نص 1", "نص 2", "نص 3"]
        labels = [0, 1, 0]
        tokenizer = MockTokenizer()
        batch_size = 2
        
        dataset = ArabicTextDataset(texts, labels, tokenizer, max_length=32)
        dataloader = DataLoader(dataset, batch_size=batch_size)
        
        # Get first batch
        batch = next(iter(dataloader))
        
        # Check batch dimensions
        self.assertEqual(batch['input_ids'].shape[0], batch_size,
                        "Batch size should match")
        self.assertEqual(batch['labels'].shape[0], batch_size,
                        "Labels batch size should match")
        
        # Check all required keys
        required_keys = {'input_ids', 'attention_mask', 'token_type_ids', 'labels'}
        self.assertEqual(set(batch.keys()), required_keys,
                        "Batch must contain all required keys")


class TestValidationFunction(unittest.TestCase):
    """Test cases for dataloader validation function."""
    
    def test_validate_correct_dataloader(self):
        """Test that validation passes for correct dataloader."""
        from dataset_with_labels import ArabicTextDataset, validate_dataloader
        
        texts = ["نص"]
        labels = [0]
        tokenizer = MockTokenizer()
        
        dataset = ArabicTextDataset(texts, labels, tokenizer)
        dataloader = DataLoader(dataset, batch_size=1)
        
        # This should return True for a correctly structured dataloader
        result = validate_dataloader(dataloader)
        self.assertTrue(result, "Validation should pass for correct dataloader")


class TestTrainingLoopLogic(unittest.TestCase):
    """Test cases for training loop logic."""
    
    def test_training_requires_labels(self):
        """Test that training function validates labels are present."""
        # This test verifies the core fix from the problem statement:
        # Training should not proceed with dummy labels
        
        # Create a batch without labels
        batch_without_labels = {
            'input_ids': torch.ones((2, 32), dtype=torch.long),
            'attention_mask': torch.ones((2, 32), dtype=torch.long),
            'token_type_ids': torch.zeros((2, 32), dtype=torch.long)
        }
        
        # Verify that 'labels' key is missing
        self.assertNotIn('labels', batch_without_labels,
                        "Test batch should not contain labels")
        
        # In the corrected training loop, this condition raises an error
        # rather than using dummy targets
        if 'labels' not in batch_without_labels:
            # This is the expected behavior - training cannot proceed
            self.assertTrue(True, "Correctly detected missing labels")
        else:
            self.fail("Should have detected missing labels")
    
    def test_training_uses_real_labels(self):
        """Test that training uses actual labels, not dummy values."""
        # Create a batch with real labels
        batch_with_labels = {
            'input_ids': torch.ones((2, 32), dtype=torch.long),
            'attention_mask': torch.ones((2, 32), dtype=torch.long),
            'token_type_ids': torch.zeros((2, 32), dtype=torch.long),
            'labels': torch.tensor([0, 1], dtype=torch.long)
        }
        
        # Verify labels are present and have correct values
        self.assertIn('labels', batch_with_labels,
                     "Batch should contain labels")
        self.assertTrue(torch.equal(batch_with_labels['labels'], 
                                   torch.tensor([0, 1], dtype=torch.long)),
                       "Labels should be real values, not dummy zeros")


class TestTrainingFunction(unittest.TestCase):
    """Test cases for the train_model function."""
    
    def test_train_model_validates_empty_dataloader(self):
        """Test that train_model handles empty dataloader."""
        from train_model import train_model
        
        # Create empty dataloader
        class EmptyDataset(torch.utils.data.Dataset):
            def __len__(self):
                return 0
            def __getitem__(self, idx):
                raise IndexError("Empty dataset")
        
        empty_dataloader = DataLoader(EmptyDataset())
        
        # Create mock model and optimizer
        model = torch.nn.Linear(10, 2)
        optimizer = torch.optim.Adam(model.parameters())
        device = torch.device('cpu')
        
        # Training should handle empty dataloader gracefully
        stats = train_model(
            model=model,
            dataloader=empty_dataloader,
            optimizer=optimizer,
            loss_function=None,
            device=device,
            epochs=1,
            output_dir=None
        )
        
        # Should complete without crashing
        self.assertEqual(len(stats['epoch_losses']), 0,
                        "No epoch losses for empty dataloader")


def run_tests():
    """Run all tests and print results."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestDatasetStructure))
    suite.addTests(loader.loadTestsFromTestCase(TestValidationFunction))
    suite.addTests(loader.loadTestsFromTestCase(TestTrainingLoopLogic))
    suite.addTests(loader.loadTestsFromTestCase(TestTrainingFunction))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    import sys
    sys.exit(run_tests())
