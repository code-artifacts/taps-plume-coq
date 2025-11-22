# TAPs Plume Coq

Complete Coq formalization of Transaction Admission Policies (TAPs) from the Plume paper at OOPSLA 2024.

## Overview

This repository contains a mechanized formalization in Coq of:
- **Definitions 1-6**: Core concepts (Transaction, History, TAP, Soundness, Completeness, Expressiveness)
- **Section 3.2 & Table 1**: Seven concrete TAP implementations (FC, C, S, D, K, R, W)
- **Theorems 2-5**: Soundness and completeness results for all TAPs

## Quick Start

```bash
# Build the project
make

# Clean build artifacts
make clean
```

## Documentation

See [SUMMARY.md](SUMMARY.md) for detailed documentation of all formalized definitions, theorems, and proofs.

## Paper Reference

**Plume: Efficient and Complete Black-Box Checking of Weak Isolation Levels**  
OOPSLA 2024  
https://hengxin.github.io/papers/2024-OOPSLA-Plume.pdf

## Status

✅ All definitions formalized  
✅ All TAPs implemented  
✅ Core theorems proven  
⚠️ Some complex proofs admitted (see SUMMARY.md)

## Requirements

- Coq 8.18 or later
- Make

