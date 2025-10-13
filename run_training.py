"""BERT Training Script for Arabic Phoneme Processing

This script implements the training pipeline for a BERT model
focused on Arabic phoneme processing with curriculum learning support.
"""

import json
import os
import sys
from pathlib import Path
from typing import Dict, Optional
import argparse

# Ensure proper UTF-8 encoding on Windows
if sys.platform == "win32":
    os.environ['PYTHONIOENCODING'] = 'utf-8'


def check_dependencies():
    """Check if all required packages are installed."""
    required_packages = [
        'transformers',
        'torch',
        'datasets',
        'pandas',
        'numpy',
        'tqdm'
    ]
    
    missing_packages = []
    for package in required_packages:
        try:
            __import__(package)
        except ImportError:
            missing_packages.append(package)
    
    if missing_packages:
        print("ERROR: Missing required packages:", ", ".join(missing_packages))
        print("\nPlease install dependencies using:")
        print("  pip install -r requirements.txt")
        return False
    
    return True


def load_config(config_path: str) -> Dict:
    """Load training configuration from JSON file."""
    if not os.path.exists(config_path):
        print(f"ERROR: Configuration file not found: {config_path}")
        sys.exit(1)
    
    with open(config_path, 'r', encoding='utf-8') as f:
        config = json.load(f)
    
    print(f"[CONFIG] Loaded configuration from {config_path}")
    return config


def prepare_dataset(config: Dict):
    """Prepare training dataset from phonemes data."""
    import pandas as pd
    from datasets import Dataset
    
    print("\n[DATASET] Preparing training dataset...")
    
    # Create data directory if it doesn't exist
    data_dir = config.get('data_dir', './data')
    os.makedirs(data_dir, exist_ok=True)
    
    # Try to load phonemes from existing CSV files
    possible_phoneme_files = [
        'الفونيمات.csv',
        'Phonemes.csv',
        'full_multilayer_grammar.csv',
        'full_multilayer_grammar1.csv'
    ]
    
    phoneme_data = []
    
    for csv_file in possible_phoneme_files:
        if os.path.exists(csv_file):
            print(f"[DATASET] Loading phonemes from {csv_file}")
            try:
                df = pd.read_csv(csv_file, encoding='utf-8-sig')
                
                # Find phoneme column
                phoneme_col = None
                for col in ['الفونيمات', 'phonemes', 'الأداة']:
                    if col in df.columns:
                        phoneme_col = col
                        break
                
                if phoneme_col:
                    # Extract phoneme texts
                    for _, row in df.iterrows():
                        phoneme = str(row[phoneme_col]).strip()
                        if phoneme and phoneme != 'nan':
                            phoneme_data.append({'text': phoneme})
                    
                    print(f"[DATASET] Loaded {len(phoneme_data)} phoneme entries")
                    break
            except Exception as e:
                print(f"[DATASET] Warning: Could not load {csv_file}: {e}")
    
    # If no data found, create sample data
    if not phoneme_data:
        print("[DATASET] No phoneme data found, creating sample data...")
        sample_texts = [
            "ا ل ح م د ل ل ه",
            "م ر ح ب ا",
            "ك ي ف ح ا ل ك",
            "ش ك ر ا",
            "أ ه ل ا و س ه ل ا"
        ]
        phoneme_data = [{'text': text} for text in sample_texts * 10]
    
    # Create train/eval split
    dataset = Dataset.from_list(phoneme_data)
    
    # Split into train and eval (80/20)
    split_dataset = dataset.train_test_split(test_size=0.2, seed=42)
    
    print(f"[DATASET] Train samples: {len(split_dataset['train'])}")
    print(f"[DATASET] Eval samples: {len(split_dataset['test'])}")
    
    return split_dataset['train'], split_dataset['test']


def create_model(config: Dict, tokenizer):
    """Create BERT model for training."""
    from transformers import BertConfig, BertForMaskedLM
    
    print("\n[MODEL] Creating BERT model...")
    
    # Configure BERT model
    model_config = BertConfig(
        vocab_size=tokenizer.vocab_size,
        hidden_size=768,
        num_hidden_layers=12,
        num_attention_heads=12,
        intermediate_size=3072,
        max_position_embeddings=config['training']['max_seq_length'],
        type_vocab_size=2,
        pad_token_id=tokenizer.vocab.get(tokenizer.pad_token, 0)
    )
    
    # Create model
    model = BertForMaskedLM(config=model_config)
    
    total_params = sum(p.numel() for p in model.parameters())
    print(f"[MODEL] Created BERT model with {total_params:,} parameters")
    
    return model


def prepare_tokenizer(config: Dict):
    """Prepare the UTF-8 phoneme tokenizer."""
    from utf8_tokenizer import create_tokenizer
    
    print("\n[TOKENIZER] Preparing UTF-8 Phoneme Tokenizer...")
    
    # Create tokenizer
    tokenizer = create_tokenizer(config)
    
    # Save tokenizer vocabulary
    tokenizer_dir = config.get('tokenizer_dir', './tokenizers')
    os.makedirs(tokenizer_dir, exist_ok=True)
    
    vocab_path = os.path.join(tokenizer_dir, 'vocab.json')
    tokenizer.save_vocab(vocab_path)
    
    print(f"[TOKENIZER] Tokenizer ready with vocab size: {tokenizer.vocab_size}")
    
    return tokenizer


def tokenize_function(examples, tokenizer, max_length):
    """Tokenize examples for training."""
    # Encode each text
    encoded = []
    for text in examples['text']:
        enc = tokenizer.encode(
            text,
            padding='max_length',
            truncation=True,
            max_length=max_length
        )
        encoded.append(enc)
    
    # Batch the results
    result = {
        'input_ids': [e['input_ids'] for e in encoded],
        'attention_mask': [e['attention_mask'] for e in encoded]
    }
    
    return result


def train_model(config: Dict, model, tokenizer, train_dataset, eval_dataset):
    """Train the BERT model."""
    from transformers import (
        Trainer,
        TrainingArguments,
    )
    import torch
    import random
    
    print("\n[TRAINING] Starting model training...")
    
    # Custom data collator for MLM
    class CustomDataCollatorForMLM:
        """Custom data collator for Masked Language Modeling."""
        
        def __init__(self, tokenizer, mlm_probability=0.15):
            self.tokenizer = tokenizer
            self.mlm_probability = mlm_probability
            self.pad_token_id = tokenizer.vocab[tokenizer.pad_token]
            self.mask_token_id = tokenizer.vocab[tokenizer.mask_token]
        
        def __call__(self, features):
            # Stack input_ids and attention_mask
            input_ids = torch.tensor([f['input_ids'] for f in features])
            attention_mask = torch.tensor([f['attention_mask'] for f in features])
            
            # Create labels (same as input_ids for MLM)
            labels = input_ids.clone()
            
            # Create random mask
            probability_matrix = torch.full(labels.shape, self.mlm_probability)
            
            # Don't mask special tokens
            special_tokens_mask = (
                (input_ids == self.pad_token_id) |
                (input_ids == self.tokenizer.vocab[self.tokenizer.cls_token]) |
                (input_ids == self.tokenizer.vocab[self.tokenizer.sep_token])
            )
            probability_matrix.masked_fill_(special_tokens_mask, value=0.0)
            
            masked_indices = torch.bernoulli(probability_matrix).bool()
            labels[~masked_indices] = -100  # Only compute loss on masked tokens
            
            # 80% of the time, replace with [MASK]
            indices_replaced = torch.bernoulli(torch.full(labels.shape, 0.8)).bool() & masked_indices
            input_ids[indices_replaced] = self.mask_token_id
            
            # 10% of the time, replace with random token
            indices_random = torch.bernoulli(torch.full(labels.shape, 0.5)).bool() & masked_indices & ~indices_replaced
            random_words = torch.randint(len(self.tokenizer.vocab), labels.shape, dtype=torch.long)
            input_ids[indices_random] = random_words[indices_random]
            
            # 10% of the time, keep original
            
            return {
                'input_ids': input_ids,
                'attention_mask': attention_mask,
                'labels': labels
            }
    
    # Prepare output directory
    output_dir = config['output_dir']
    os.makedirs(output_dir, exist_ok=True)
    
    # Prepare log directory
    log_dir = config.get('logging', {}).get('log_dir', './logs')
    os.makedirs(log_dir, exist_ok=True)
    
    # Training arguments
    training_config = config['training']
    training_args = TrainingArguments(
        output_dir=output_dir,
        num_train_epochs=training_config['num_train_epochs'],
        per_device_train_batch_size=training_config['per_device_train_batch_size'],
        per_device_eval_batch_size=training_config['per_device_eval_batch_size'],
        learning_rate=training_config['learning_rate'],
        warmup_steps=training_config['warmup_steps'],
        weight_decay=training_config['weight_decay'],
        logging_dir=log_dir,
        logging_steps=training_config['logging_steps'],
        save_steps=training_config['save_steps'],
        eval_steps=training_config['eval_steps'],
        save_total_limit=training_config['save_total_limit'],
        gradient_accumulation_steps=training_config['gradient_accumulation_steps'],
        eval_strategy="steps",  # Changed from evaluation_strategy
        save_strategy="steps",
        load_best_model_at_end=True,
        report_to=[],  # Disable reporting to avoid tensorboard requirement
        fp16=torch.cuda.is_available(),  # Use mixed precision if GPU available
    )
    
    # Tokenize datasets
    max_length = training_config['max_seq_length']
    
    print("[TRAINING] Tokenizing datasets...")
    tokenized_train = train_dataset.map(
        lambda x: tokenize_function(x, tokenizer, max_length),
        batched=True,
        remove_columns=train_dataset.column_names
    )
    
    tokenized_eval = eval_dataset.map(
        lambda x: tokenize_function(x, tokenizer, max_length),
        batched=True,
        remove_columns=eval_dataset.column_names
    )
    
    # Data collator for MLM
    data_collator = CustomDataCollatorForMLM(
        tokenizer=tokenizer,
        mlm_probability=0.15
    )
    
    # Create trainer
    trainer = Trainer(
        model=model,
        args=training_args,
        train_dataset=tokenized_train,
        eval_dataset=tokenized_eval,
        data_collator=data_collator,
    )
    
    # Train
    print("[TRAINING] Training started...")
    print(f"[TRAINING] Device: {'GPU' if torch.cuda.is_available() else 'CPU'}")
    
    trainer.train()
    
    print("\n[TRAINING] Training completed!")
    
    # Save final model
    final_model_path = os.path.join(output_dir, "final_model")
    trainer.save_model(final_model_path)
    tokenizer.save_vocab(os.path.join(final_model_path, "vocab.json"))
    
    print(f"[TRAINING] Model saved to {final_model_path}")
    
    return trainer


def curriculum_training(config: Dict, model, tokenizer, train_dataset, eval_dataset):
    """Implement curriculum training with progressive complexity."""
    curriculum_config = config.get('curriculum_training', {})
    
    if not curriculum_config.get('enabled', False):
        print("[CURRICULUM] Curriculum training disabled, using standard training")
        return train_model(config, model, tokenizer, train_dataset, eval_dataset)
    
    print("\n[CURRICULUM] Starting curriculum training...")
    
    stages = curriculum_config.get('stages', [])
    
    for idx, stage in enumerate(stages):
        print(f"\n[CURRICULUM] Stage {idx + 1}/{len(stages)}: {stage['name']}")
        print(f"[CURRICULUM] Max length: {stage['max_length']}, Epochs: {stage['epochs']}")
        
        # Update config for this stage
        stage_config = config.copy()
        stage_config['training']['max_seq_length'] = stage['max_length']
        stage_config['training']['num_train_epochs'] = stage['epochs']
        stage_config['output_dir'] = f"{config['output_dir']}/stage_{idx + 1}_{stage['name']}"
        
        # Train for this stage
        trainer = train_model(stage_config, model, tokenizer, train_dataset, eval_dataset)
        
        # Update model for next stage
        model = trainer.model
    
    print("\n[CURRICULUM] Curriculum training completed!")
    return trainer


def main():
    """Main training function."""
    parser = argparse.ArgumentParser(description='Train BERT model for Arabic phoneme processing')
    parser.add_argument(
        '--config',
        type=str,
        default='config/training_config.json',
        help='Path to training configuration file'
    )
    parser.add_argument(
        '--skip-deps-check',
        action='store_true',
        help='Skip dependency checking'
    )
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("BERT Training for Arabic Phoneme Processing")
    print("=" * 70)
    
    # Check dependencies
    if not args.skip_deps_check:
        if not check_dependencies():
            print("\nInstalling dependencies...")
            os.system(f"{sys.executable} -m pip install -r requirements.txt")
            print("\nDependencies installed. Please run the script again.")
            return
    
    # Load configuration
    config = load_config(args.config)
    
    # Prepare tokenizer
    tokenizer = prepare_tokenizer(config)
    
    # Prepare dataset
    train_dataset, eval_dataset = prepare_dataset(config)
    
    # Create model
    model = create_model(config, tokenizer)
    
    # Check if curriculum training is enabled
    if config.get('curriculum_training', {}).get('enabled', False):
        trainer = curriculum_training(config, model, tokenizer, train_dataset, eval_dataset)
    else:
        trainer = train_model(config, model, tokenizer, train_dataset, eval_dataset)
    
    print("\n" + "=" * 70)
    print("Training Pipeline Completed Successfully!")
    print("=" * 70)
    print(f"\nModel saved to: {config['output_dir']}")
    print(f"Logs saved to: {config.get('logging', {}).get('log_dir', './logs')}")
    print("\nTo use the trained model:")
    print("  from transformers import BertForMaskedLM")
    print(f"  model = BertForMaskedLM.from_pretrained('{config['output_dir']}/final_model')")


if __name__ == '__main__':
    main()
