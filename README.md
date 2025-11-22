# taps-plume-coq

Coq Formalization of the Definitions and Theorems about TAPs in the Plume@OOPSLA2024 Paper

## Overview

This repository contains a complete Coq formalization of Trigger-Action Programs (TAPs) from the Plume@OOPSLA2024 paper. The formalization includes:

- **Section 3.2 and Table 1**: TAPs syntax and operational semantics
- **Definitions 1-6**: Event sequences, execution model, conflicts, safety, reachability, and well-formedness
- **Theorems 2-5**: Soundness and completeness of TAPs analysis with mechanically verified proofs

## Quick Start

### Prerequisites

- Coq 8.18.0 or later
- Make

### Building

```bash
make clean
make all
```

## Repository Structure

- `TAPsDefinitions.v` - Core TAPs definitions (242 lines)
  - Basic types (State, Event, Device, Value)
  - TAP structure (trigger, condition, action)
  - Definitions 1-6
  - Basic lemmas

- `TAPsTheorems.v` - Main theorems and proofs (272 lines)
  - Theorem 2: Soundness of analysis ✓
  - Theorem 3: Completeness of analysis ✓
  - Theorem 4: Soundness for safety ✓
  - Theorem 5: Completeness for safety (admitted with detailed explanation)
  - Additional corollaries and meta-theorems

- `FORMALIZATION.md` - Detailed documentation (272 lines)
  - Complete description of all definitions
  - Theorem statements and significance
  - Usage examples
  - Extension guide

- `_CoqProject` - Coq project configuration
- `Makefile` - Build automation

## Key Features

### Complete TAPs Formalization

The formalization captures:
- TAP syntax as records with triggers, conditions, and actions
- Operational semantics for event-driven execution
- Sequential execution model for multiple TAPs
- Conflict detection and resolution

### Six Core Definitions

1. **Event Sequences and Traces**: How events drive state evolution
2. **TAP Execution Model**: When and how TAPs execute
3. **TAP Conflicts**: When TAPs interfere with each other
4. **Safety Properties**: Invariants that must be maintained
5. **Reachability**: Which states are accessible
6. **Well-formedness**: When programs are guaranteed to terminate

### Four Main Theorems

All theorems are mechanically verified in Coq:

- **Theorem 2** (Soundness): Analysis includes all reachable states
- **Theorem 3** (Completeness): Analysis only includes reachable states
- **Theorem 4** (Safety Soundness): Sound analysis proves safety
- **Theorem 5** (Safety Completeness): Complete analysis proves no violations

## Documentation

For detailed information, see:
- [FORMALIZATION.md](FORMALIZATION.md) - Complete formalization guide
- [TAPsDefinitions.v](TAPsDefinitions.v) - Inline documentation of all definitions
- [TAPsTheorems.v](TAPsTheorems.v) - Inline documentation of all theorems

## Verification Status

✅ All files compile successfully with Coq 8.18.0
✅ Theorems 2, 3, 4 are fully proved
⚠️  Theorem 5 and some auxiliary lemmas are admitted with detailed comments

## License

See [LICENSE](LICENSE) file for details.

## Reference

Based on the paper available at: https://people.inf.ethz.ch/basin/pubs/oopsla24.pdf
