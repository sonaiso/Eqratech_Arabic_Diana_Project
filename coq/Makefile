# FractalHub Coq Formalization Makefile

.PHONY: all clean theories extraction

# Default target
all: theories

# Build all theories
theories:
	@echo "Building Coq theories..."
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

# Extract to OCaml
extraction: theories
	@echo "Extracting to OCaml..."
	coqc -R theories FractalHub theories/Extraction.v
	@echo "Extracted code available in fractalhub_kernel.ml"

# Clean build artifacts
clean:
	@echo "Cleaning..."
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/*.aux
	rm -f *.ml *.mli
	rm -f .*.aux

# Verify all proofs
verify: theories
	@echo "All proofs verified ✓"

# Help
help:
	@echo "FractalHub Coq Formalization"
	@echo ""
	@echo "Targets:"
	@echo "  all        - Build all Coq theories (default)"
	@echo "  theories   - Build all Coq theories"
	@echo "  extraction - Extract to OCaml"
	@echo "  verify     - Verify all proofs"
	@echo "  clean      - Remove build artifacts"
	@echo "  help       - Show this help"
