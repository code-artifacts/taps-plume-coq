(** * Coq Formalization of TAPs Definitions *)
(** This file formalizes the definitions of Trigger-Action Programs (TAPs)
    from Section 3.2 and Table 1 of the Plume@OOPSLA2024 paper,
    along with Definitions 1-6. *)

Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Logic.
Require Import Classical.
Require Import ClassicalChoice.
Import ListNotations.

(** ** Basic Types *)

(** State of the system *)
Parameter State : Type.

(** Events that can occur *)
Parameter Event : Type.

(** Device identifiers *)
Parameter Device : Type.

(** Values that can be stored in the state *)
Parameter Value : Type.

(** Decidable equality for states *)
Parameter state_eq_dec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.

(** Decidable equality for events *)
Parameter event_eq_dec : forall (e1 e2 : Event), {e1 = e2} + {e1 <> e2}.

(** ** Section 3.2: TAPs Syntax and Semantics *)

(** Conditions are predicates over states *)
Definition Condition := State -> Prop.

(** Decidable conditions for computation *)
Parameter condition_dec : forall (c : Condition) (s : State), {c s} + {~c s}.

(** Actions are state transformers *)
Definition Action := State -> State.

(** A TAP consists of a trigger event, a condition, and an action
    Table 1: TAP = (trigger, condition, action) *)
Record TAP : Type := mkTAP {
  trigger : Event;
  condition : Condition;
  action : Action
}.

(** A TAP program is a list of TAPs *)
Definition TAPProgram := list TAP.

(** Operational semantics: a TAP executes when its trigger event occurs
    and the condition holds, resulting in a state transformation *)
Definition tap_executes (tap : TAP) (e : Event) (s : State) : Prop :=
  e = trigger tap /\ condition tap s.

Definition tap_apply (tap : TAP) (s : State) : State :=
  action tap s.

(** ** Definition 1: Event Sequences and Traces *)

(** An event sequence is a list of events *)
Definition EventSeq := list Event.

(** A trace is a sequence of states resulting from event execution *)
Definition Trace := list State.

(** Initial state *)
Parameter init_state : State.

(** Event semantics: how an event changes the state *)
Parameter event_semantics : Event -> State -> State.

(** Execute a single event on a state *)
Definition exec_event (e : Event) (s : State) (prog : TAPProgram) : State :=
  fold_left (fun s' tap =>
    if event_eq_dec e (trigger tap) then
      if condition_dec (condition tap) s' then
        tap_apply tap s'
      else s'
    else s')
    prog s.

(** Generate a trace from an event sequence *)
Fixpoint gen_trace (events : EventSeq) (s : State) (prog : TAPProgram) : Trace :=
  match events with
  | [] => [s]
  | e :: es => s :: gen_trace es (exec_event e s prog) prog
  end.

(** ** Definition 2: TAP Execution Model *)

(** A TAP is enabled if its trigger and condition are satisfied *)
Definition tap_enabled (tap : TAP) (e : Event) (s : State) : Prop :=
  tap_executes tap e s.

(** Multiple TAPs can be enabled simultaneously *)
Definition enabled_taps (prog : TAPProgram) (e : Event) (s : State) : list TAP :=
  filter (fun tap => 
    if event_eq_dec e (trigger tap) then
      if condition_dec (condition tap) s then true else false
    else false) prog.

(** Sequential execution model: TAPs execute in program order *)
Fixpoint exec_taps_seq (taps : list TAP) (s : State) : State :=
  match taps with
  | [] => s
  | tap :: rest => exec_taps_seq rest (tap_apply tap s)
  end.

(** ** Definition 3: TAP Conflicts *)

(** Two TAPs conflict if they can be enabled by the same event
    and produce different outcomes *)
Definition taps_conflict (tap1 tap2 : TAP) : Prop :=
  trigger tap1 = trigger tap2 /\
  exists s : State,
    condition tap1 s /\ condition tap2 s /\
    tap_apply tap1 (tap_apply tap2 s) <> tap_apply tap2 (tap_apply tap1 s).

(** A program is conflict-free if no two TAPs conflict *)
Definition conflict_free (prog : TAPProgram) : Prop :=
  forall tap1 tap2,
    In tap1 prog -> In tap2 prog -> tap1 <> tap2 ->
    ~taps_conflict tap1 tap2.

(** ** Definition 4: Safety Properties *)

(** A safety property is a predicate over states *)
Definition SafetyProperty := State -> Prop.

(** A state is safe with respect to a property *)
Definition state_safe (s : State) (prop : SafetyProperty) : Prop :=
  prop s.

(** A trace is safe if all states satisfy the property *)
Definition trace_safe (tr : Trace) (prop : SafetyProperty) : Prop :=
  forall s, In s tr -> state_safe s prop.

(** A program maintains a safety property if all reachable states are safe *)
Definition maintains_safety (prog : TAPProgram) (events : EventSeq) 
                           (prop : SafetyProperty) : Prop :=
  trace_safe (gen_trace events init_state prog) prop.

(** ** Definition 5: Reachability *)

(** A state is reachable if there exists an event sequence that leads to it *)
Definition reachable (prog : TAPProgram) (s : State) : Prop :=
  exists events : EventSeq,
    In s (gen_trace events init_state prog).

(** The set of all reachable states *)
Definition reachable_states (prog : TAPProgram) : State -> Prop :=
  fun s => reachable prog s.

(** ** Definition 6: Well-formedness *)

(** A TAP is well-formed if its action always terminates *)
Definition tap_well_formed (tap : TAP) : Prop :=
  forall s : State, exists s' : State, s' = tap_apply tap s.

(** A program is well-formed if all TAPs are well-formed *)
Definition program_well_formed (prog : TAPProgram) : Prop :=
  forall tap, In tap prog -> tap_well_formed tap.

(** ** Additional Auxiliary Definitions *)

(** Deterministic execution: same events lead to same states *)
Definition deterministic (prog : TAPProgram) : Prop :=
  forall events s1 s2,
    gen_trace events s1 prog = gen_trace events s2 prog ->
    s1 = s2.

(** TAP commutativity *)
Definition taps_commute (tap1 tap2 : TAP) : Prop :=
  forall s : State,
    tap_apply tap1 (tap_apply tap2 s) = tap_apply tap2 (tap_apply tap1 s).

(** Program satisfies property initially *)
Definition initially_safe (prop : SafetyProperty) : Prop :=
  state_safe init_state prop.

(** Invariant preservation *)
Definition preserves_invariant (tap : TAP) (prop : SafetyProperty) : Prop :=
  forall s : State,
    state_safe s prop ->
    state_safe (tap_apply tap s) prop.

(** Program preserves invariant *)
Definition program_preserves_invariant (prog : TAPProgram) 
                                       (prop : SafetyProperty) : Prop :=
  forall tap, In tap prog -> preserves_invariant tap prop.

(** ** Basic Lemmas *)

(** Empty trace is safe *)
Lemma empty_trace_safe : forall prop,
  trace_safe [] prop.
Proof.
  intros prop s H. contradiction.
Qed.

(** Singleton trace safety *)
Lemma singleton_trace_safe : forall s prop,
  state_safe s prop -> trace_safe [s] prop.
Proof.
  intros s prop H_safe s' H_in.
  simpl in H_in. destruct H_in as [H_eq | H_false].
  - rewrite <- H_eq. assumption.
  - contradiction.
Qed.

(** Trace safety is preserved by cons *)
Lemma trace_safe_cons : forall s tr prop,
  state_safe s prop -> trace_safe tr prop ->
  trace_safe (s :: tr) prop.
Proof.
  intros s tr prop H_s H_tr s' H_in.
  simpl in H_in. destruct H_in as [H_eq | H_in_rest].
  - rewrite <- H_eq. assumption.
  - apply H_tr. assumption.
Qed.

(** Well-formed TAP produces a state *)
Lemma well_formed_tap_produces_state : forall tap s,
  tap_well_formed tap ->
  exists s', s' = tap_apply tap s.
Proof.
  intros tap s H_wf. apply H_wf.
Qed.

(** If a program is well-formed, each TAP is well-formed *)
Lemma program_well_formed_tap : forall prog tap,
  program_well_formed prog ->
  In tap prog ->
  tap_well_formed tap.
Proof.
  intros prog tap H_prog H_in.
  unfold program_well_formed in H_prog.
  apply H_prog. assumption.
Qed.
