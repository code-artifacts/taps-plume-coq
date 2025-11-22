(** * Example TAPs Programs and Proofs *)
(** This file demonstrates the use of the TAPs formalization
    with concrete examples. *)

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import TAPsDefinitions.
Require Import TAPsTheorems.

(** ** Example 1: Simple Smart Home TAPs *)

Section SmartHomeExample.

  (** Define some concrete events *)
  Parameter doorbell_ring : Event.
  Parameter motion_detected : Event.
  Parameter door_opened : Event.

  (** Define some conditions *)
  Parameter is_daytime : Condition.
  Parameter is_authorized : Condition.
  Parameter lights_off : Condition.

  (** Define some actions *)
  Parameter unlock_door : Action.
  Parameter turn_on_lights : Action.
  Parameter send_notification : Action.

  (** Define TAPs *)
  Definition tap_auto_unlock : TAP := 
    mkTAP doorbell_ring is_authorized unlock_door.

  Definition tap_motion_lights : TAP :=
    mkTAP motion_detected lights_off turn_on_lights.

  Definition tap_door_notify : TAP :=
    mkTAP door_opened is_daytime send_notification.

  (** A simple smart home program *)
  Definition smart_home_program : TAPProgram :=
    [tap_auto_unlock; tap_motion_lights; tap_door_notify].

  (** Prove that each TAP is well-formed *)
  Axiom unlock_terminates : forall s, exists s', s' = unlock_door s.
  Axiom lights_terminate : forall s, exists s', s' = turn_on_lights s.
  Axiom notify_terminates : forall s, exists s', s' = send_notification s.

  Lemma tap_auto_unlock_wf : tap_well_formed tap_auto_unlock.
  Proof.
    unfold tap_well_formed. simpl. intros s.
    apply unlock_terminates.
  Qed.

  Lemma tap_motion_lights_wf : tap_well_formed tap_motion_lights.
  Proof.
    unfold tap_well_formed. simpl. intros s.
    apply lights_terminate.
  Qed.

  Lemma tap_door_notify_wf : tap_well_formed tap_door_notify.
  Proof.
    unfold tap_well_formed. simpl. intros s.
    apply notify_terminates.
  Qed.

  (** The smart home program is well-formed *)
  Theorem smart_home_well_formed : program_well_formed smart_home_program.
  Proof.
    unfold program_well_formed, smart_home_program.
    intros tap H_in.
    simpl in H_in.
    destruct H_in as [H1 | [H2 | [H3 | H_false]]].
    - rewrite <- H1. apply tap_auto_unlock_wf.
    - rewrite <- H2. apply tap_motion_lights_wf.
    - rewrite <- H3. apply tap_door_notify_wf.
    - contradiction.
  Qed.

End SmartHomeExample.

(** ** Example 2: Safety Properties *)

Section SafetyExample.

  (** Define a safety property: door is never unlocked when not authorized *)
  Parameter door_locked : State -> Prop.
  Parameter user_authorized : State -> Prop.

  Definition door_safety : SafetyProperty :=
    fun s => door_locked s \/ user_authorized s.

  (** Assume the initial state is safe *)
  Axiom init_door_safe : state_safe init_state door_safety.

  Lemma initial_door_safety : initially_safe door_safety.
  Proof.
    unfold initially_safe.
    apply init_door_safe.
  Qed.

  (** If we can prove the program preserves this invariant,
      then all reachable states are safe *)
  Theorem safety_by_invariant : forall (prog : TAPProgram),
    program_well_formed prog ->
    program_preserves_invariant prog door_safety ->
    forall events,
      trace_safe (gen_trace events init_state prog) door_safety.
  Proof.
    intros prog H_wf H_pres events.
    (* This would follow from invariant_preservation_theorem, which is admitted.
       We admit this as well to demonstrate the concept. *)
  Admitted.

End SafetyExample.

(** ** Example 3: Conflict Analysis *)

Section ConflictExample.

  Parameter light_event : Event.
  Parameter room_occupied : Condition.
  Parameter room_empty : Condition.
  Parameter turn_on : Action.
  Parameter turn_off : Action.

  (** Two TAPs that respond to the same trigger *)
  Definition tap_turn_on : TAP :=
    mkTAP light_event room_occupied turn_on.

  Definition tap_turn_off : TAP :=
    mkTAP light_event room_empty turn_off.

  (** If the conditions are mutually exclusive, there's no conflict *)
  Axiom conditions_exclusive : forall s,
    room_occupied s -> ~room_empty s.

  Lemma no_conflict_when_exclusive :
    ~taps_conflict tap_turn_on tap_turn_off.
  Proof.
    unfold taps_conflict.
    intro H_conflict.
    destruct H_conflict as [H_same_trigger H_exists].
    destruct H_exists as [s [H_occ [H_empty H_neq]]].
    apply conditions_exclusive in H_occ.
    contradiction.
  Qed.

  (** Therefore, a program with these TAPs is conflict-free *)
  Theorem light_program_conflict_free :
    conflict_free [tap_turn_on; tap_turn_off].
  Proof.
    unfold conflict_free.
    intros tap1 tap2 H_in1 H_in2 H_neq.
    simpl in H_in1, H_in2.
    (* Case analysis on which TAPs we're comparing *)
    destruct H_in1 as [H_eq1 | [H_eq2 | []]]; 
    destruct H_in2 as [H_eq1' | [H_eq2' | []]];
    subst.
    - (* tap1 = tap_turn_on, tap2 = tap_turn_on *)
      contradiction.
    - (* tap1 = tap_turn_on, tap2 = tap_turn_off *)
      apply no_conflict_when_exclusive.
    - (* tap1 = tap_turn_off, tap2 = tap_turn_on *)
      intro H_conflict.
      unfold taps_conflict in H_conflict.
      destruct H_conflict as [H_trigger H_exists].
      destruct H_exists as [s [H_empty [H_occ H_neq']]].
      apply conditions_exclusive in H_occ.
      contradiction.
    - (* tap1 = tap_turn_off, tap2 = tap_turn_off *)
      contradiction.
  Qed.

End ConflictExample.

(** ** Example 4: Reachability Analysis *)

Section ReachabilityExample.

  (** A state is reachable if we can construct an event sequence leading to it *)
  Lemma init_reachable : forall prog,
    reachable prog init_state.
  Proof.
    intro prog.
    unfold reachable.
    exists [].
    simpl. left. reflexivity.
  Qed.

  (** If a state is in a trace generated from some events, it's reachable *)
  Lemma trace_states_reachable : forall prog events s,
    In s (gen_trace events init_state prog) ->
    reachable prog s.
  Proof.
    intros prog events s H_in.
    unfold reachable.
    exists events. assumption.
  Qed.

End ReachabilityExample.

(** ** Example 5: Using Analysis for Verification *)

Section VerificationExample.

  (** If we have sound and complete analysis, we can precisely verify properties *)
  Theorem precise_safety_verification : forall prog prop,
    program_well_formed prog ->
    analysis_sound prog ->
    analysis_complete prog ->
    initially_safe prop ->
    (forall s, analyze prog s -> state_safe s prop) <->
    (forall s, reachable prog s -> state_safe s prop).
  Proof.
    intros prog prop H_wf H_sound H_complete H_init.
    apply precise_verification; assumption.
  Qed.

  (** This means checking safety on the analysis result is equivalent
      to checking it on all reachable states *)

End VerificationExample.

(** ** Summary *)

(** This file demonstrates:
    1. How to define concrete TAPs with events, conditions, and actions
    2. How to prove programs are well-formed
    3. How to work with safety properties and invariants
    4. How to analyze conflicts between TAPs
    5. How to reason about reachability
    6. How to use sound and complete analysis for verification
*)
