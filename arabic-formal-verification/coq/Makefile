# ============================================================
# Makefile for SFGCOQ - Arabic Grammar Formal Verification
# ============================================================

COQC = coqc
COQDEP = coqdep
COQFLAGS = -Q . ArabicGrammar

# Source files in dependency order
SOURCES = ArabicGrammar.v NawasighRules.v MorphologyRules.v

# Compiled files
OBJECTS = $(SOURCES:.v=.vo)

# Default target
all: $(OBJECTS)

# Compile each .v file
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# Dependencies
ArabicGrammar.vo: ArabicGrammar.v
NawasighRules.vo: NawasighRules.v ArabicGrammar.vo
MorphologyRules.vo: MorphologyRules.v ArabicGrammar.vo

# Generate dependency file
.depend: $(SOURCES)
	$(COQDEP) $(COQFLAGS) $(SOURCES) > .depend

# Clean compiled files
clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .depend

# Verify all proofs
verify: all
	@echo "✓ All proofs verified successfully!"

# Help
help:
	@echo "SFGCOQ - Arabic Grammar Formal Verification"
	@echo "============================================"
	@echo ""
	@echo "Available targets:"
	@echo "  all     - Compile all COQ files"
	@echo "  verify  - Verify all proofs"
	@echo "  clean   - Remove compiled files"
	@echo "  help    - Show this help message"
	@echo ""
	@echo "Usage:"
	@echo "  make        # Compile all"
	@echo "  make clean  # Clean"
	@echo "  make verify # Verify proofs"

.PHONY: all clean verify help
