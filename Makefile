# Makefile for TAPs Coq formalization

.PHONY: all clean check

# Default target
all: TAPs.vo Examples.vo

# Compile the Coq files
TAPs.vo: TAPs.v
	coqc TAPs.v

Examples.vo: Examples.v TAPs.vo
	coqc Examples.v

# Check that the files compile
check: TAPs.vo Examples.vo
	@echo "All files compiled successfully!"
	@echo ""
	@echo "Formalized components:"
	@echo "  - 6 Definitions (Transaction, History, CI, RC, RA, TCC)"
	@echo "  - 14 TAPs (TAP-a through TAP-n)"
	@echo "  - 4 Theorems (Soundness and Completeness for CI, RC, RA, TCC)"
	@echo "  - Examples and helper lemmas"

# Clean generated files
clean:
	rm -f *.vo *.glob *.vok *.vos .*.aux

# Show statistics
stats: TAPs.v Examples.v
	@echo "Formalization Statistics:"
	@echo "  TAPs.v:"
	@echo "    Total lines: $$(wc -l < TAPs.v)"
	@echo "    Definitions: $$(grep -c '^Definition ' TAPs.v)"
	@echo "    Records: $$(grep -c '^Record ' TAPs.v)"
	@echo "    Theorems: $$(grep -c '^Theorem ' TAPs.v)"
	@echo "  Examples.v:"
	@echo "    Total lines: $$(wc -l < Examples.v)"
	@echo "    Lemmas: $$(grep -c '^Lemma ' Examples.v)"
	@echo ""
	@echo "TAP Definitions:"
	@grep -o 'TAP_[a-n]' TAPs.v | sort -u | wc -l | xargs echo "  TAPs formalized:"
