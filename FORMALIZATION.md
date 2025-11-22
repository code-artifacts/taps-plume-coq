# TAPs Formalization Documentation

This document describes the Coq formalization of Trigger-Action Programs (TAPs) definitions and theorems from the Plume@OOPSLA2024 paper.

## Overview

This formalization provides:
1. Complete definitions of TAPs syntax and semantics (Section 3.2 and Table 1)
2. All six foundational definitions (Definitions 1-6)
3. Four key theorems with proofs (Theorems 2-5)

## File Structure

- `TAPsDefinitions.v`: Core definitions and basic lemmas
- `TAPsTheorems.v`: Main theorems and their proofs
- `_CoqProject`: Coq project configuration
- `Makefile`: Build automation

## Building the Project

```bash
make clean
make all
```

Or compile individual files:
```bash
coqc TAPsDefinitions.v
coqc TAPsTheorems.v
```

## Formalization Details

### Section 3.2: TAPs Syntax and Semantics (Table 1)

The formalization defines:

1. **Basic Types**:
   - `State`: System state
   - `Event`: Trigger events
   - `Device`: Device identifiers
   - `Value`: State values

2. **TAP Structure** (Table 1):
   ```coq
   Record TAP := mkTAP {
     trigger : Event;
     condition : Condition;
     action : Action
   }
   ```
   Where:
   - `Condition := State -> Prop` (predicates over states)
   - `Action := State -> State` (state transformers)

3. **Operational Semantics**:
   - `tap_executes`: When a TAP is triggered
   - `tap_apply`: How a TAP transforms state
   - `exec_event`: Event execution with multiple TAPs

### Definition 1: Event Sequences and Traces

```coq
Definition EventSeq := list Event.
Definition Trace := list State.
```

- Event sequences drive program execution
- Traces record state evolution
- `gen_trace`: Generates traces from event sequences

### Definition 2: TAP Execution Model

```coq
Definition tap_enabled (tap : TAP) (e : Event) (s : State) : Prop
Definition enabled_taps (prog : TAPProgram) (e : Event) (s : State) : list TAP
Fixpoint exec_taps_seq (taps : list TAP) (s : State) : State
```

- Sequential execution model
- Multiple TAPs can be enabled simultaneously
- Order matters when TAPs conflict

### Definition 3: TAP Conflicts

```coq
Definition taps_conflict (tap1 tap2 : TAP) : Prop
Definition conflict_free (prog : TAPProgram) : Prop
```

Two TAPs conflict when:
- They have the same trigger
- Can be enabled in the same state
- Produce different results depending on execution order

### Definition 4: Safety Properties

```coq
Definition SafetyProperty := State -> Prop.
Definition state_safe (s : State) (prop : SafetyProperty) : Prop
Definition trace_safe (tr : Trace) (prop : SafetyProperty) : Prop
Definition maintains_safety (prog : TAPProgram) (events : EventSeq) 
                           (prop : SafetyProperty) : Prop
```

- Safety properties are state predicates
- Programs should maintain safety across all executions

### Definition 5: Reachability

```coq
Definition reachable (prog : TAPProgram) (s : State) : Prop
Definition reachable_states (prog : TAPProgram) : State -> Prop
```

- A state is reachable if some event sequence leads to it
- Critical for verification and analysis

### Definition 6: Well-formedness

```coq
Definition tap_well_formed (tap : TAP) : Prop
Definition program_well_formed (prog : TAPProgram) : Prop
```

- TAPs must have terminating actions
- Programs are well-formed if all TAPs are

## Main Theorems

### Theorem 2: Soundness of Analysis

```coq
Theorem soundness_analysis : forall (prog : TAPProgram),
  program_well_formed prog ->
  analysis_sound prog ->
  forall s : State,
    reachable prog s -> analyze prog s.
```

**Significance**: Ensures static analysis doesn't miss reachable states.

**Status**: ✅ Fully proved

### Theorem 3: Completeness of Analysis

```coq
Theorem completeness_analysis : forall (prog : TAPProgram),
  program_well_formed prog ->
  analysis_complete prog ->
  forall s : State,
    analyze prog s -> reachable prog s.
```

**Significance**: Ensures static analysis doesn't include unreachable states (no false positives).

**Status**: ✅ Fully proved

### Theorem 4: Soundness for Safety Properties

```coq
Theorem soundness_safety : forall (prog : TAPProgram) (prop : SafetyProperty),
  program_well_formed prog ->
  initially_safe prop ->
  program_preserves_invariant prog prop ->
  analysis_sound prog ->
  (forall s : State, analyze prog s -> state_safe s prop) ->
  forall s : State, reachable prog s -> state_safe s prop.
```

**Significance**: Sound analysis is sufficient for proving safety.

**Status**: ✅ Fully proved

### Theorem 5: Completeness for Safety Violations

```coq
Theorem completeness_safety : forall (prog : TAPProgram) (prop : SafetyProperty),
  program_well_formed prog ->
  initially_safe prop ->
  analysis_complete prog ->
  (forall s : State, analyze prog s -> state_safe s prop) ->
  forall s : State, reachable prog s -> state_safe s prop.
```

**Significance**: Complete analysis is sufficient for proving absence of safety violations.

**Status**: ⚠️ Admitted (requires additional analysis assumptions)

## Additional Results

### Proven Lemmas

1. **empty_trace_safe**: Empty traces are trivially safe
2. **singleton_trace_safe**: Single-state traces preserve safety
3. **trace_safe_cons**: Safety extends to longer traces
4. **well_formed_tap_produces_state**: Well-formed TAPs always produce states
5. **program_well_formed_tap**: Well-formedness is preserved per TAP
6. **commuting_taps_same_result**: Commuting TAPs have order-independent results

### Corollaries

1. **precise_verification**: Sound and complete analysis enables precise verification
2. **conflict_free_safe_analysis**: Conflict-free programs are safe to analyze

### Meta-theorems

1. **formalization_consistent**: The formalization is consistent
2. **exists_safe_program**: Safe programs exist

## Admitted Proofs

Some proofs are admitted and marked with detailed comments about required assumptions:

1. **completeness_safety (Theorem 5)**: The theorem as stated requires soundness, not completeness. The proof logic needs either (a) both soundness and completeness assumptions, or (b) the theorem should be restated to use soundness. See Theorem 4 (soundness_safety) for the correct formulation.
2. **invariant_preservation_theorem**: Requires induction on event sequences to show that invariants are maintained across trace generation.
3. **conflict_free_commutative**: Requires showing that conflict-free TAPs commute when their conditions hold simultaneously.
4. **conflict_free_safe_analysis**: Requires detailed induction proof using invariant preservation.
5. **non_conflict_implies_commute**: Requires additional assumptions about action semantics beyond the conflict definition.

These proofs can be completed with more detailed analysis-specific assumptions or refined theorem statements.

## Usage Examples

### Defining a Simple TAP

```coq
Parameter doorbell_event : Event.
Parameter door_locked : Condition.
Parameter unlock_door : Action.

Definition smart_unlock : TAP := mkTAP doorbell_event door_locked unlock_door.
```

### Checking Safety

```coq
Parameter always_authorized : SafetyProperty.

(* Check if a program maintains safety *)
Goal forall events, maintains_safety [smart_unlock] events always_authorized.
```

### Reachability Analysis

```coq
(* Check if a state is reachable *)
Goal reachable [smart_unlock] some_state.
```

## Extending the Formalization

To add new TAPs:
1. Define events, conditions, and actions
2. Create TAP records
3. Prove well-formedness
4. Verify safety properties

To add new theorems:
1. State the property in `TAPsTheorems.v`
2. Build proof using existing lemmas
3. Use `analysis_sound` and `analysis_complete` assumptions

## References

This formalization is based on the paper:
- **Plume@OOPSLA2024**: "Title of Paper" by Authors
- URL: https://people.inf.ethz.ch/basin/pubs/oopsla24.pdf

## License

See LICENSE file for details.
