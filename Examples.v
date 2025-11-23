(** * Examples and Documentation for TAPs Formalization

    This file provides additional documentation and would be the place
    to add concrete examples of histories that exhibit specific TAPs.
*)

Require Import TAPs.
Require Import Coq.Arith.PeanoNat.

(** * Example Usage

    To use the formalization, one would typically:
    
    1. Define concrete keys, values, and transaction IDs
    2. Construct operations (Read and Write)
    3. Build transactions with their program orders
    4. Create a history with the transactions and relations
    5. Check if the history satisfies various isolation levels
    6. Check if the history exhibits specific TAPs
*)

(** * Concrete Instantiation Example *)

Section Examples.

(** Instantiate keys as natural numbers *)
Definition concrete_key := nat.
Definition concrete_key_eq_dec := Nat.eq_dec.

(** Instantiate values as natural numbers *)
Definition concrete_value := nat.
Definition concrete_value_eq_dec := Nat.eq_dec.

(** Instantiate transaction IDs as natural numbers *)
Definition concrete_txn_id := nat.
Definition concrete_txn_id_eq_dec := Nat.eq_dec.

(** * Example TAP Violations

    Below we would construct concrete examples showing:
    - A history that violates TAP-j (non-repeatable read)
    - A history that violates TAP-g (cyclic causality)
    - A history that violates TAP-c (future read)
    
    Each example would:
    1. Define specific transactions with operations
    2. Build a history connecting them
    3. Prove that the history exhibits the TAP
*)

(** Example: A history exhibiting TAP-j (Non-repeatable read)
    
    Transaction t reads key x twice, getting different values:
    t: R(x, 1) ... R(x, 2)
    t1: W(x, 1)
    t2: W(x, 2)
    
    With WR edges: t1 --WR(x)--> t and t2 --WR(x)--> t
    This violates cut isolation.
*)

End Examples.

(** * Helper Lemmas

    For complete proofs, we would need lemmas such as:
*)

(** If a history has no TAP-j, then it satisfies cut isolation *)
Lemma no_tap_j_implies_ci : forall H,
  ~TAP_j H -> CutIsolation H.
Proof.
  intros H Hno_tap.
  (* This is the completeness direction of Theorem 2 *)
  apply CI_soundness_completeness. assumption.
Qed.

(** If a history satisfies cut isolation, it has no TAP-j *)
Lemma ci_implies_no_tap_j : forall H,
  CutIsolation H -> ~TAP_j H.
Proof.
  intros H Hci.
  (* This is the soundness direction of Theorem 2 *)
  apply CI_soundness_completeness. assumption.
Qed.

(** * Relationships Between Isolation Levels

    The paper establishes a hierarchy:
    CI ⊊ RC ⊊ RA ⊊ TCC
    
    These could be formally proven in Coq.
*)

(** Read Atomicity is stronger than Read Committed *)
Lemma RA_implies_RC : forall H,
  ReadAtomicity H -> ReadCommitted H.
Proof.
  intros H HRA.
  unfold ReadAtomicity in HRA.
  destruct HRA as [HRC1 [HRC2 [HRC3 [CM [HCM HReadAtomic]]]]].
  unfold ReadCommitted.
  split. assumption.
  split. assumption.
  split. assumption.
  exists CM. split. assumption.
  (* MonoAtomicView follows from ReadAtomic *)
  admit.
Admitted.

(** Transactional Causal Consistency is stronger than Read Atomicity *)
Lemma TCC_implies_RA : forall H,
  TransactionalCausalConsistency H -> ReadAtomicity H.
Proof.
  intros H HTCC.
  unfold TransactionalCausalConsistency in HTCC.
  destruct HTCC as [HRC1 [HRC2 [HRC3 [CM [HCM HCausal]]]]].
  unfold ReadAtomicity.
  split. assumption.
  split. assumption.
  split. assumption.
  exists CM. split. assumption.
  (* ReadAtomic follows from Causal *)
  admit.
Admitted.

(** * Properties of TAPs

    Various properties about TAPs and their relationships
*)

(** If a history has TAP-h, it also has TAP-i (for some CM) *)
Lemma TAP_h_implies_TAP_i : forall H CM,
  commit_order H CM ->
  TAP_h H ->
  TAP_i H CM.
Proof.
  intros H CM HCM HTAP_h.
  unfold TAP_h in HTAP_h.
  unfold TAP_i.
  (* TAP-h is a special case of TAP-i where CO ordering exists *)
  admit.
Admitted.

(** * Utility Lemmas for Operations and Transactions *)

(** Helper: If an operation is a read, it's not a write *)
Lemma read_not_write : forall o,
  is_read o -> ~is_write o.
Proof.
  intros o. destruct o; simpl; auto.
Qed.

(** Helper: If an operation is a write, it's not a read *)  
Lemma write_not_read : forall o,
  is_write o -> ~is_read o.
Proof.
  intros o. destruct o; simpl; auto.
Qed.

(** * Notes on Extending the Formalization

    To make the proofs fully mechanized:
    
    1. Add axioms ensuring histories are well-formed:
       - Every read has a corresponding write
       - WR relation is consistent with operation values
       - SO and WR relations respect transaction membership
    
    2. Prove properties about strict orders:
       - Irreflexivity
       - Transitivity  
       - Asymmetry
       - Trichotomy (for total orders)
    
    3. Add lemmas about transitive closure:
       - Properties of clos_trans
       - Relationship between CO and SO ∪ WR
    
    4. Prove the main theorems by:
       - For soundness: Show each axiom violation leads to a TAP
       - For completeness: Show absence of TAPs allows constructing
         the required orders (CM, CO) that satisfy the axioms
*)
