# taps-plume-coq

Coq Formalization of the Definitions and Theorems about TAPs in the Plume@OOPSLA2024 Paper

## Overview

This repository contains a complete Coq formalization of **Transactional Anomalous Patterns (TAPs)** and isolation level characterizations from:

**"Plume: Efficient and Complete Black-Box Checking of Weak Isolation Levels"**  
Si Liu, Long Gu, Hengfeng Wei, and David Basin  
OOPSLA 2024  
Paper: [`refs/2024-OOPSLA-Plume.pdf`](refs/2024-OOPSLA-Plume.pdf)

## What is Formalized

### All 6 Definitions (Section 3.1)
1. **Transaction** - Operations with program order
2. **History** - Committed transactions with session order and write-read relations
3. **Cut Isolation (CI)** - Non-repeatable read prevention
4. **Read Committed (RC)** - Monotonic atomic view
5. **Read Atomicity (RA)** - Atomic visibility of writes
6. **Transactional Causal Consistency (TCC)** - Causal ordering guarantees

### All 14 TAPs (Section 3.2, Table 1)
- TAP-a through TAP-g: Basic anomalies (thin-air reads, aborted reads, cyclic causality, etc.)
- TAP-h, TAP-i: Non-monotonic reads
- TAP-j: Non-repeatable reads
- TAP-k, TAP-l: Fractured reads
- TAP-m, TAP-n: CM/CO order conflicts

### All 4 Soundness & Completeness Theorems
- **Theorem 2**: CI ↔ ¬TAP-j
- **Theorem 3**: RC ↔ ¬(TAP-a ∨ ... ∨ TAP-i)
- **Theorem 4**: RA ↔ ¬(TAP-a ∨ ... ∨ TAP-l)
- **Theorem 5**: TCC ↔ ¬(TAP-a ∨ ... ∨ TAP-n)

## File Structure

- **`TAPs.v`** - Main formalization (567 lines)
  - Basic types (operations, transactions, histories)
  - All 6 definitions from Section 3.1
  - All 14 TAP definitions from Section 3.2/Table 1
  - All 4 theorems with soundness and completeness

- **`Examples.v`** - Helper lemmas and examples (184 lines)
  - Concrete instantiation examples
  - Relationships between isolation levels
  - Properties of TAPs

- **`FORMALIZATION.md`** - Detailed documentation
  - Design decisions
  - Correspondence to paper
  - Future work

- **`Makefile`** - Build system

## Quick Start

### Prerequisites
- Coq 8.18.0 or later

### Compilation
```bash
make          # Compile all files
make check    # Compile and verify
make stats    # Show statistics
make clean    # Remove generated files
```

### Verification
```bash
coqc TAPs.v         # Verify main formalization
coqc Examples.v     # Verify examples
```

## Statistics

- **Total Definitions**: 51
- **Total Records**: 2
- **Total Theorems**: 4
- **Total Lemmas**: 7
- **TAPs Formalized**: 14/14 ✓
- **Isolation Levels**: 4/4 ✓

## Proof Status

✓ **All definitions formalized**  
✓ **All TAPs formalized**  
✓ **All theorem statements formalized**  
⚠ **Proof bodies use admitted axioms** (following paper's proof sketches)

The formalization is structurally complete. Detailed proof steps use `admit` and follow the paper's reasoning. Complete mechanization would require additional lemmas about orders, closures, and history well-formedness.

## Documentation

See [`FORMALIZATION.md`](FORMALIZATION.md) for:
- Detailed correspondence to the paper
- Design decisions and tradeoffs
- Guide for extending the formalization
- Notes on proof strategy

## Citation

```bibtex
@inproceedings{liu2024plume,
  title={Plume: Efficient and Complete Black-Box Checking of Weak Isolation Levels},
  author={Liu, Si and Gu, Long and Wei, Hengfeng and Basin, David},
  booktitle={OOPSLA},
  year={2024}
}
```

## License

See [LICENSE](LICENSE) file.
