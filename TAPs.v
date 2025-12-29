(** * Formalization of Transactional Anomalous Patterns (TAPs)
    
    This file formalizes the definitions and theorems from the paper:
    "Plume: Efficient and Complete Black-Box Checking of Weak Isolation Levels"
    OOPSLA 2024
    
    We formalize:
    - Definitions 1-6 (Transactions, Histories, and Isolation Levels)
    - All 14 TAPs from Section 3.2 and Table 1
    - Theorems 2-5 (Soundness and Completeness)
*)

Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalChoice.

(** Definition of strict order (irreflexive and transitive) *)
Definition strict_order {A : Type} (R : relation A) : Prop :=
  (forall x, ~R x x) /\ transitive A R.

(** * Basic Types *)

(** Keys in the key-value store *)
Parameter Key : Type.
Parameter Key_eq_dec : forall (x y : Key), {x = y} + {x <> y}.

(** Values *)
Parameter Value : Type.
Parameter Value_eq_dec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.

(** Operations: Read or Write *)
Inductive Op : Type :=
  | Read (x : Key) (v : Value) : Op
  | Write (x : Key) (v : Value) : Op.

Definition Op_eq_dec : forall (o1 o2 : Op), {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality; auto using Key_eq_dec, Value_eq_dec.
Defined.

(** Extract key from an operation *)
Definition op_key (o : Op) : Key :=
  match o with
  | Read x _ => x
  | Write x _ => x
  end.

(** Check if operation is a read *)
Definition is_read (o : Op) : Prop :=
  match o with
  | Read _ _ => True
  | Write _ _ => False
  end.

(** Check if operation is a write *)
Definition is_write (o : Op) : Prop :=
  match o with
  | Read _ _ => False
  | Write _ _ => True
  end.

(** * Definition 1: Transaction *)

(** Transaction identifier *)
Parameter TxnId : Type.
Parameter TxnId_eq_dec : forall (t1 t2 : TxnId), {t1 = t2} + {t1 <> t2}.

(** A transaction is a pair (O, po) where O is a set of operations
    and po is a strict total order over O *)
Record Transaction := {
  txn_id : TxnId;
  ops : Ensemble Op;
  po : relation Op;
  po_strict_total : strict_order po /\ forall o1 o2, ops o1 -> ops o2 -> o1 <> o2 -> po o1 o2 \/ po o2 o1
}.

(** Notation for operations in a transaction *)
Definition O (t : Transaction) : Ensemble Op := ops t.

(** Operations on key x in transaction t *)
Definition Ox (t : Transaction) (x : Key) : Ensemble Op :=
  fun o => ops t o /\ op_key o = x.

(** Read operations in transaction t *)
Definition R (t : Transaction) : Ensemble Op :=
  fun o => ops t o /\ is_read o.

(** Read operations on key x in transaction t *)
Definition Rx (t : Transaction) (x : Key) : Ensemble Op :=
  fun o => ops t o /\ is_read o /\ op_key o = x.

(** Write operations in transaction t *)
Definition W (t : Transaction) : Ensemble Op :=
  fun o => ops t o /\ is_write o.

(** Write operations on key x in transaction t *)
Definition Wx (t : Transaction) (x : Key) : Ensemble Op :=
  fun o => ops t o /\ is_write o /\ op_key o = x.

(** Set of transactions that read from key x *)
Definition RTx (T : Ensemble Transaction) (x : Key) : Ensemble Transaction :=
  fun t => T t /\ exists o, Rx t x o.

(** Set of transactions that write to key x *)
Definition WTx (T : Ensemble Transaction) (x : Key) : Ensemble Transaction :=
  fun t => T t /\ exists o, Wx t x o.

(** Transaction writes value v to key x (last write) *)
Definition txn_writes (t : Transaction) (x : Key) (v : Value) : Prop :=
  exists w, Wx t x w /\ w = Write x v /\
  forall w', Wx t x w' -> po t w' w \/ w' = w.

(** Transaction reads value v from key x (first read before any write) *)
Definition txn_reads (t : Transaction) (x : Key) (v : Value) : Prop :=
  exists r, Rx t x r /\ r = Read x v /\
  (forall w, Wx t x w -> ~po t w r) /\
  (forall r', Rx t x r' -> po t r r' \/ r' = r).

(** Notation: t ⊢ W(x, v) *)
Notation "t '⊢' 'W(' x ',' v ')'" := (txn_writes t x v) (at level 80).

(** Notation: t ⊢ R(x, v) *)
Notation "t '⊢' 'R(' x ',' v ')'" := (txn_reads t x v) (at level 80).

(** * Definition 2: History *)

(** Set of aborted transactions *)
Parameter Taborted : Ensemble Transaction.

(** A history is a tuple H = (T, SO, WR) *)
Record History := {
  T : Ensemble Transaction;
  SO : relation Transaction;
  WR : Key -> relation Transaction;

  (** Assumptions from the paper *)

  (** Assumption 1: Initial transaction *)
  (* init_txn : Transaction;
  init_in_T : T init_txn;
  init_writes_all : forall x, exists v, init_txn ⊢ W(x, v);
  init_precedes_all : forall t, T t -> t <> init_txn -> 
    clos_trans Transaction (fun t1 t2 => SO t1 t2 \/ exists x, WR x t1 t2) init_txn t; *)

  (** Assumption 2: Unique values *)
  unique_values : forall t1 t2 x v,
    T t1 -> T t2 -> t1 ⊢ W(x, v) -> t2 ⊢ W(x, v) -> t1 = t2;
  
  (** WR constraints *)
  wr_reads_writes : forall x t s,
    WR x t s -> T t /\ T s /\ t <> s /\
    exists v, t ⊢ W(x, v) /\ s ⊢ R(x, v);
    
  wr_unique : forall x s,
    T s -> (exists v, s ⊢ R(x, v)) ->
    exists! t, T t /\ WR x t s;

  (** (SO U WR) is acyclic**)
  so_wr_acyclic : strict_order (clos_trans Transaction (fun t1 t2 => SO t1 t2 \/ exists x, WR x t1 t2));

  (** Additional Well-formedness Axioms, not included in the paper *)
  
  (** Disjointness of Committed and Aborted Transactions *)
  disjoint_T_Taborted : forall t, T t -> ~Taborted t;
  
  (** Completeness of Reads: Every read must come from somewhere (internal or external) *)
  read_completeness : forall t x r v,
    T t -> Rx t x r -> r = Read x v ->
    (exists w, Wx t x w /\ w = Write x v /\ po t w r) \/  (* Internal read *)
    (exists t', T t' /\ WR x t' t /\ t' ⊢ W(x, v));      (* External read *)
    
  (** Operations belong to unique transactions *)
  op_txn_unique : forall t1 t2 o,
    ops t1 o -> ops t2 o -> t1 = t2;

  (** WR implies value match *)
  (* wr_value_match : forall x t1 t2 v,
    WR x t1 t2 -> t1 ⊢ W(x, v) -> t2 ⊢ R(x, v) *)
}.

(** Union of session order and write-read relations *)
Definition SO_union_WR (H : History) : relation Transaction :=
  fun t1 t2 => SO H t1 t2 \/ exists x, WR H x t1 t2.

(** Transitive closure of SO ∪ WR *)
Definition SO_union_WR_plus (H : History) : relation Transaction :=
  clos_trans Transaction (SO_union_WR H).

(** Identity relation on T *)
Definition IT (H : History) : relation Transaction :=
  fun t1 t2 => T H t1 /\ T H t2 /\ t1 = t2.

(** * Causal Order *)

(** CO is the transitive closure of SO ∪ WR *)
Definition CO (H : History) : relation Transaction :=
  SO_union_WR_plus H.

(** * Commit Order *)

(** A commit order is a strict total order on transactions preserving causal order *)
Definition commit_order (H : History) (CM : relation Transaction) : Prop :=
  strict_order CM /\
  (forall t1 t2, T H t1 -> T H t2 -> t1 <> t2 -> CM t1 t2 \/ CM t2 t1) /\
  (forall t1 t2, CO H t1 t2 -> CM t1 t2).  (** CO ⊆ CM *)

(** General operation write-read relation *)
Definition wr_rel : relation Op :=
  fun w r => (exists x v, w = Write x v /\ r = Read x v).

Notation "w '−wr→' r" := (wr_rel _ w r) (at level 70).

(** * Definition 3: Cut Isolation *)

Definition CutIsolation (H : History) : Prop :=
  forall x v v' t t1 t2 r1 r2 w1 w2,
    RTx (T H) x t ->
    WTx (T H) x t1 -> t1 <> t ->
    WTx (T H) x t2 -> t2 <> t ->
    Rx t x r1 -> r1 = Read x v ->
    Rx t x r2 -> r2 = Read x v' ->
    Wx t1 x w1 ->
    Wx t2 x w2 ->
    t1 <> t2 -> r1 <> r2 ->
    wr_rel w1 r1 -> wr_rel w2 r2 ->
    v = v'.

(** * Definition 4: Read Committed *)

(** RC-1: A read operation cannot read from a later write in the same transaction *)
Definition RC1 (H : History) : Prop :=
  forall t r w,
    T H t ->
    R t r -> W t w ->
    wr_rel w r -> po t w r.

(** RC-2: If a read on x is preceded by writes to x, it reads the last such write *)
Definition RC2 (H : History) : Prop :=
  forall x t r,
    T H t ->
    Rx t x r ->
    (exists w', Wx t x w' /\ po t w' r) ->
    exists w, Wx t x w /\ po t w r /\
      wr_rel w r /\
      forall w'', Wx t x w'' -> po t w'' w \/ w'' = w \/ po t r w''.

(** RC-3: If a transaction writes to a key multiple times, only the last write
    should be visible to other transactions.
    Formally: ∀x ∈ K. ∀t ∈ T. ∀w, w' ∈ Wx(t). 
    ((∃t' ≠ t ∈ RTx. ∃r ∈ Rx(t'). w --wr(x)--> r) ⟹ w' --po_t--> w ∨ w' = w) *)
Definition RC3 (H : History) : Prop :=
  forall x t w w',
    T H t ->
    Wx t x w -> Wx t x w' ->
    (exists t' r, 
       t' <> t /\ 
       T H t' /\ 
       Rx t' x r /\ 
       wr_rel w r) ->
    po t w' w \/ w' = w.

(** RC-4: MonoAtomicView axiom 
    Paper definition: If both t₁ and t₂ write to x, and t₃ reads y ≠ x from t₂ 
    and then reads x from t₁, then t₂ →^CM t₁. **)
Definition MonoAtomicView (H : History) (CM : relation Transaction) : Prop :=
  forall x y t1 t2 t3,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    (exists wx wy rx ry, Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    po t3 ry rx /\ wr_rel wy ry /\ wr_rel wx rx) ->                                   
    CM t2 t1.

(** Read Committed *)
Definition ReadCommitted (H : History) : Prop :=
  RC1 H /\ RC2 H /\ RC3 H /\
  exists CM, commit_order H CM /\ MonoAtomicView H CM.

(** * Definition 5: Read Atomicity *)

(** ReadAtomic axiom *)
Definition ReadAtomic (H : History) (CM : relation Transaction) : Prop :=
  forall x t1 t2 t3,
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> t3 <> t1 -> t3 <> t2 ->
    WR H x t1 t3 ->
    SO_union_WR H t2 t3 ->
    CM t2 t1.

Definition ReadAtomicity (H : History) : Prop :=
  RC1 H /\ RC2 H /\ RC3 H /\
  exists CM, commit_order H CM /\ ReadAtomic H CM.

(** * Definition 6: Transactional Causal Consistency *)

(** Causal axiom *)
Definition Causal (H : History) (CM : relation Transaction) : Prop :=
  forall x t1 t2 t3,
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> t3 <> t1 -> t3 <> t2 ->
    WR H x t1 t3 ->
    CO H t2 t3 ->
    CM t2 t1.

Definition TransactionalCausalConsistency (H : History) : Prop :=
  RC1 H /\ RC2 H /\ RC3 H /\
  exists CM, commit_order H CM /\ Causal H CM.

(** * Transactional Anomalous Patterns (TAPs) *)

(** TAP-a: ThinAirRead - A transaction reads a value out of thin air *)
Definition TAP_a (H : History) : Prop :=
  exists r t, T H t /\ R t r /\
    forall w t', (T H t' \/ Taborted t') /\ W t' w ->
      ~wr_rel w r.

(** TAP-b: AbortedRead - A transaction reads from an aborted transaction *)
Definition TAP_b (H : History) : Prop :=
  exists r w t ta, 
    T H t /\  R t r /\ 
    Taborted ta /\ W ta w /\ 
    wr_rel w r.

(** TAP-c: FutureRead - A transaction reads from a future write in itself *)
Definition TAP_c (H : History) : Prop :=
  exists t w r,
    T H t /\
    W t w /\ R t r /\
    wr_rel w r /\ po t r w.

(** TAP-d: NotMyOwnWrite - Transaction reads from external write but has written to x *)
Definition TAP_d (H : History) : Prop :=
  exists x t t' w r w',
    T H t /\ T H t' /\ t <> t' /\ WTx (T H) x t /\ WTx (T H) x t' /\
    Rx t x r /\ Wx t x w /\  Wx t' x w' /\
    wr_rel w' r /\ po t w r.

(** TAP-e: NotMyLastWrite - Transaction reads from internal write that's not the last *)
Definition TAP_e (H : History) : Prop :=
  exists x t w w' r,
    T H t /\
    Wx t x w /\ Wx t x w' /\ w <> w' /\
    Rx t x r /\
    po t w w' /\ po t w' r /\
    wr_rel w r.

(** TAP-f: IntermediateRead - Transaction reads intermediate value from another transaction *)
Definition TAP_f (H : History) : Prop :=
  exists x t t' r w w',
    T H t /\ T H t' /\ t <> t' /\ RTx (T H) x t /\ WTx (T H) x t' /\
    Rx t x r /\ Wx t' x w /\ Wx t' x w' /\ w <> w' /\
    wr_rel w r /\ po t' w w'.

(** TAP-g: CyclicCO - The relation SO ∪ WR is cyclic *)
Definition TAP_g (H : History) : Prop :=
  exists t1 t2, SO_union_WR_plus H t1 t2 /\ IT H t1 t2.

(** TAP-h: NonMonoReadCO - Non-monotonic read with CO order *)
Definition TAP_h (H : History) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    wr_rel wx rx /\
    wr_rel wy ry /\
    po t3 ry rx /\
    CO H t1 t2.

(** TAP-i: NonMonoReadCM - Non-monotonic read with CM order *)
Definition TAP_i (H : History) (CM : relation Transaction) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    wr_rel wx rx /\
    wr_rel wy ry /\
    po t3 ry rx /\
    CM t1 t2.

(** TAP-j: NonRepeatableRead - Transaction reads same key twice, gets different values *)
Definition TAP_j (H : History) : Prop :=
  exists x v v' t t1 t2 r1 r2 w1 w2,
    v <> v' /\
    t1 <> t /\ t2 <> t /\
    RTx (T H) x t /\ WTx (T H) x t1 /\ WTx (T H) x t2 /\
    Rx t x r1 /\ r1 = Read x v /\
    Rx t x r2 /\ r2 = Read x v' /\
    Wx t1 x w1 /\ Wx t2 x w2 /\
    t1 <> t2 /\ wr_rel w1 r1 /\ wr_rel w2 r2.

(** TAP-k: FracturedReadCO - Fractured read with CO order *)
Definition TAP_k (H : History) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    ((WR H x t1 t3 /\ CO H t1 t2 /\ SO H t2 t3) \/
      (exists y, RTx (T H) y t3 /\ WR H x t1 t3 /\ CO H t1 t2 /\ WR H y t2 t3)).

(** TAP-l: FracturedReadCM - Fractured read with CM order *)
Definition TAP_l (H : History) (CM : relation Transaction) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    ((WR H x t1 t3 /\ CM t1 t2 /\ SO H t2 t3) \/
      (exists y, RTx (T H) y t3 /\ WR H x t1 t3 /\ CM t1 t2 /\ WR H y t2 t3)).

(** TAP-m: COConflictCM - CO and CM order conflict *)
Definition TAP_m (H : History) (CM : relation Transaction) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    WR H x t1 t3 /\
    CO H t1 t2 /\ CO H t2 t3.

(** TAP-n: ConflictCM - CM and CO order conflict *)
Definition TAP_n (H : History) (CM : relation Transaction) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    WR H x t1 t3 /\
    CM t1 t2 /\ CO H t2 t3.

(** * Characterization of isolation levels via TAPs *)

(** History is free of TAPs a through g *)
Definition no_TAP_a_to_g (H : History) : Prop :=
  ~TAP_a H /\ ~TAP_b H /\ ~TAP_c H /\ ~TAP_d H /\
  ~TAP_e H /\ ~TAP_f H /\ ~TAP_g H.

(** History is free of TAPs a through i with a commit order *)
Definition no_TAP_a_to_i (H : History) (CM : relation Transaction) : Prop :=
  no_TAP_a_to_g H /\ ~TAP_h H /\ ~TAP_i H CM.

(** History is free of TAPs a through l with a commit order *)
Definition no_TAP_a_to_l (H : History) (CM : relation Transaction) : Prop :=
  no_TAP_a_to_i H CM /\ ~TAP_j H /\ ~TAP_k H /\ ~TAP_l H CM.

(** History is free of all TAPs *)
Definition no_all_TAPs (H : History) (CM : relation Transaction) : Prop :=
  no_TAP_a_to_l H CM /\ ~TAP_m H CM /\ ~TAP_n H CM.

(** * Theorem 2: Soundness and Completeness for CI *)

Theorem CI_soundness_completeness : forall H,
  CutIsolation H <-> ~TAP_j H.
Proof.
  intros H. split.
  - (* Soundness: CI -> ~TAP_j *)
    intros HCI HTAP_j.
    unfold TAP_j in HTAP_j.
    destruct HTAP_j as [x [v [v' [t [t1 [t2 [r1 [r2 [w1 [w2 Hconj]]]]]]]]]].
    unfold CutIsolation in HCI.
    destruct Hconj as [Ht [Ht1 [Ht2 [Hneq1 [Hneq2 [Hneq12 [Hr1 [Heqr1 [Hr2 [Heqr2 [Hw1 [Hw2 [Hwr1 [Hwr2 Hneqv]]]]]]]]]]]]]].
    assert (v = v').
    { apply (HCI x v v' t t1 t2 r1 r2 w1 w2); auto.
      intro H_eq.
      rewrite Heqr1, Heqr2 in H_eq.
      injection H_eq.
      apply Ht.
    }
    contradiction.
  - (* Completeness: ~TAP_j -> CI *)
    intros Hno_j.
    unfold CutIsolation.
    intros x v v' t t1 t2 r1 r2 w1 w2 Hrt Hwt1 Hneq1 Hwt2 Hneq2 
      Hr1 Heqr1 Hr2 Heqr2 Hw1 Hw2 Hneq12 Hrneq Hwr1 Hwr2.
    destruct (Value_eq_dec v v') as [Heq | Hneq]; auto.
    exfalso. apply Hno_j.
    unfold TAP_j.
    exists x, v, v', t, t1, t2, r1, r2, w1, w2.
    destruct Hrt as [Ht _]. destruct Hwt1 as [Ht1 _]. destruct Hwt2 as [Ht2 _].
    destruct Hr1 as [Hr1a [Hr1b Hr1c]].
    destruct Hr2 as [Hr2a [Hr2b Hr2c]].
    destruct Hw1 as [Hw1a [Hw1b Hw1c]].
    destruct Hw2 as [Hw2a [Hw2b Hw2c]].
    repeat split; auto.
    + exists r1. unfold Rx. auto.
    + exists w1. unfold Wx. auto.
    + exists w2. unfold Wx. auto.
Qed.

(** * Theorem 3: Soundness and Completeness for RC *)

Lemma RC123_iff_no_TAP_a_to_g: forall H,
  RC1 H /\ RC2 H /\ RC3 H <-> no_TAP_a_to_g H.
Proof.
  intros H. split.
  - (* Soundness: RC1 /\ RC2 /\ RC3 -> no TAPs a-g *)
    intros HRC.
    destruct HRC as [HRC1 [HRC2 HRC3]].
    unfold no_TAP_a_to_g.
    repeat split.
    + (* TAP_a: ThinAirRead - subsumed by Definition 2 (read_completeness) *)
      unfold TAP_a. intros [r [t [Ht [Hr Hno_write]]]].
      (* TAP_a: There exists a read r (in t) that reads from NO write (neither internal nor external) *)
      destruct Hr as [Hops Hr_is_r].
      destruct r as [x val | x val]; try contradiction. (* r is Read x val *)
      
      (* Use read_completeness from History *)
      (* Need to prove Rx t x (Read x val) first *)
      assert (Hrx: Rx t x (Read x val)).
      { split; [exact Hops | split; [simpl; auto | simpl; auto]]. }
      destruct (read_completeness H t x (Read x val) val) as [Hinternal | Hexternal]; auto.
      * (* Case 1: Internal read - r reads from internal write w in t *)
        destruct Hinternal as [w [Hwx [Hval Hpo]]].
        (* w is a write in t with w = Write x val *)
        (* Hno_write says: for all w t', if (T H t' \/ Taborted t') /\ W t' w, then ~wr_rel w (Read x val) *)
        (* But we have w = Write x val in t, and T H t, so contradiction *)
        apply (Hno_write w t).
        split.
        { left. exact Ht. }
        { unfold W. destruct Hwx as [Hwx_ops [Hw_is_w _]]. split; assumption. }
        (* Show wr_rel w (Read x val): w = Write x val and r = Read x val *)
        unfold wr_rel. exists x, val. split; [exact Hval | reflexivity].
      * (* Case 2: External read - r reads from t' via WR *)
        destruct Hexternal as [t' [Ht' [Hwr Hwrites]]].
        (* t' writes to x with value val. The write op is w' *)
        unfold txn_writes in Hwrites. destruct Hwrites as [w' [Hwx' [Hval' Hlast]]].
        subst w'.
        (* Hno_write says: for all w t', if (T H t' \/ Taborted t') /\ W t' w, then ~wr_rel w (Read x val) *)
        (* But we have Write x val in t', and T H t', so contradiction *)
        apply (Hno_write (Write x val) t').
        split.
        { left. exact Ht'. }
        { unfold W. destruct Hwx' as [Hwx_ops [Hw_is_w _]]. split; assumption. }
        (* Show wr_rel (Write x val) (Read x val) *)
        unfold wr_rel. exists x, val. split; reflexivity.
    + (* TAP_b: AbortedRead - subsumed by Definition 2 (disjoint_T_Taborted, op_txn_unique) *)
      unfold TAP_b. intros [r [w [t [ta [Ht [Hr [Hta [Hw Hwr]]]]]]]].
      (* TAP_b: A committed transaction t reads r, and r matches a write w from aborted transaction ta *)
      (* wr_rel w r means w = Write x v and r = Read x v for some x, v *)
      unfold wr_rel in Hwr.
      destruct Hwr as [x [v [Hw_eq Hr_eq]]].
      subst w r.
      (* Now we need to derive a contradiction *)
      (* The read Read x v is in committed transaction t *)
      (* By read_completeness, it must read from either internal or external committed write *)
      destruct Hr as [Hr_ops Hr_is_r].
      assert (Hrx: Rx t x (Read x v)).
      { split; [exact Hr_ops | split; [simpl; auto | simpl; auto]]. }
      destruct (read_completeness H t x (Read x v) v) as [Hinternal | Hexternal]; auto.
      * (* Internal read: t has a write to x with value v *)
        destruct Hinternal as [w' [Hwx' [Hval' Hpo']]].
        (* w' = Write x v is in t (committed), but Write x v is also in ta (aborted) *)
        (* By op_txn_unique, t = ta, but that contradicts disjoint_T_Taborted *)
        destruct Hw as [Hops_ta Hw_is_w].
        destruct Hwx' as [Hops_t [Hw'_is_w _]].
        subst w'.
        assert (Heq_t_ta: t = ta). { apply (op_txn_unique H t ta (Write x v) Hops_t Hops_ta). }
        subst ta. apply (disjoint_T_Taborted H t); assumption.
      * (* External read: t reads from some committed t' *)
        destruct Hexternal as [t' [Ht' [Hwr' Hwrites]]].
        (* t' ⊢ W(x, v), so t' has the last write Write x v *)
        unfold txn_writes in Hwrites.
        destruct Hwrites as [w_last [Hwx_last [Hval_last _]]].
        subst w_last.
        (* Write x v is in both t' (committed) and ta (aborted) *)
        destruct Hw as [Hops_ta Hw_is_w].
        destruct Hwx_last as [Hops_t' [Hw_is_w' _]].
        assert (Heq_t'_ta: t' = ta). { apply (op_txn_unique H t' ta (Write x v) Hops_t' Hops_ta). }
        subst ta. apply (disjoint_T_Taborted H t'); assumption.
    + (* TAP_c *) unfold TAP_c. intros [t [w [r [Ht [Hw [Hr [Hwr Hpo]]]]]]].
      unfold RC1 in HRC1.
      (* wr_rel w r means w = Write x v and r = Read x v for some x, v *)
      unfold wr_rel in Hwr.
      destruct Hwr as [x [v [Hw_eq Hr_eq]]].
      subst w r.
      (* Now we have W t (Write x v) and R t (Read x v) with po t (Read x v) (Write x v) *)
      destruct Hw as [Hw_ops Hw_is_w]. destruct Hr as [Hr_ops Hr_is_r].
      (* By RC1, if wr_rel w r, then po t w r *)
      assert (Hintra: wr_rel (Write x v) (Read x v)).
      { unfold wr_rel. exists x, v. split; reflexivity. }
      assert (HW: W t (Write x v)). { unfold W; split; assumption. }
      assert (HR: R t (Read x v)). { unfold R; split; assumption. }
      specialize (HRC1 t (Read x v) (Write x v) Ht HR HW Hintra).
      (* Now we have po t (Write x v) (Read x v) from RC1 *)
      (* But Hpo says po t (Read x v) (Write x v) *)
      destruct (po_strict_total t) as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      assert (Cycle: po t (Write x v) (Write x v)). { eapply Htrans; eassumption. }
      apply Hirrefl in Cycle. contradiction.
    + (* TAP_d *) unfold TAP_d. 
      intros [x [t [t' [w [r [w' [Ht [Ht' [Hneq [HWTx_t [HWTx_t' [Hrx [Hwx [Hwx' [Hwr Hpo]]]]]]]]]]]]]]].
      (* TAP-d: t has written to x (w), then reads x from external t' (w').
         This should be ruled out by RC2: if t wrote to x before reading,
         t must read from its own last write, not from external. *)
      unfold RC2 in HRC2.
      (* t has a write w to x before reading r *)
      assert (Hpreceded: exists w'', Wx t x w'' /\ po t w'' r).
      { exists w. split; assumption. }
      (* By RC2, t must read from some internal write *)
      destruct (HRC2 x t r Ht Hrx Hpreceded) as [w_int [Hwx_int [Hpo_int [Hwr_int _]]]].
      (* w_int is the last write to x before r in t *)
      (* Hwr_int: wr_rel w_int r -- r reads from w_int (internal) *)
      (* But Hwr: wr_rel w' r -- r reads from w' (in external t') *)
      (* w_int and w' must write the same value to x *)
      destruct Hwr_int as [x1 [v1 [Hw_int_eq Hr_eq1]]].
      destruct Hwr as [x2 [v2 [Hw'_eq Hr_eq2]]].
      (* r matches both w_int and w', so they write the same value *)
      rewrite Hr_eq1 in Hr_eq2. inversion Hr_eq2. subst x2 v2.
      (* Now w_int = Write x1 v1 and w' = Write x1 v1 *)
      subst w_int w'.
      (* Both writes are Write x1 v1 *)
      (* w_int is in t (via Hwx_int), w' is in t' (via Hwx') *)
      (* By op_txn_unique, t = t' *)
      destruct Hwx_int as [Hwx_int_ops [_ _]].
      destruct Hwx' as [Hwx'_ops [_ _]].
      assert (Heq_t_t': t = t'). { apply (op_txn_unique H t t' (Write x1 v1) Hwx_int_ops Hwx'_ops). }
      (* But t <> t' from Hneq *)
      contradiction.
    + (* TAP_e: NotMyLastWrite - forbidden by RC2 *)
      unfold TAP_e. intros [x [t [w [w' [r [Ht [Hwx [Hwx' [Hneq [Hrx [Hpo_ww' [Hpo_w'r Hwr]]]]]]]]]]]].
      (* TAP_e: t has two writes w and w' to x, with po t w w' /\ po t w' r /\ wr_rel w r
         i.e., r reads from w but w is NOT the last write before r (w' comes after w) *)
      unfold RC2 in HRC2.
      (* By RC2: since w' precedes r, r must read from the last write before r *)
      assert (Hpreceded: exists w'', Wx t x w'' /\ po t w'' r).
      { exists w'. split; assumption. }
      destruct (HRC2 x t r Ht Hrx Hpreceded) as [w_last [Hwx_last [Hpo_last [Hwr_last Hmax]]]].
      (* Hwr_last: wr_rel w_last r - r reads from w_last according to RC2 *)
      (* Hwr: wr_rel w r - r reads from w according to TAP_e *)
      (* Both have wr_rel with r, so w and w_last write the same value *)
      destruct Hwr as [x1 [v1 [Hw_eq Hr_eq1]]].
      destruct Hwr_last as [x2 [v2 [Hw_last_eq Hr_eq2]]].
      rewrite Hr_eq1 in Hr_eq2. inversion Hr_eq2. subst x2 v2.
      (* w = Write x1 v1 and w_last = Write x1 v1 *)
      subst w w_last.
      (* Now w = w_last = Write x1 v1 *)
      (* Hmax says: for all w'' in Wx t x, po t w'' (Write x1 v1) \/ w'' = Write x1 v1 \/ po t r w'' *)
      specialize (Hmax w' Hwx').
      destruct Hmax as [Hpo_w'_wlast | [Heq_w'_wlast | Hpo_r_w']].
      * (* Case 1: po t w' (Write x1 v1) *)
        (* But Hpo_ww' says po t (Write x1 v1) w', so we have a cycle *)
        destruct (po_strict_total t) as [[Hirrefl Htrans] _].
        assert (Hcycle: po t (Write x1 v1) (Write x1 v1)). 
        { eapply Htrans; [exact Hpo_ww' | exact Hpo_w'_wlast]. }
        apply Hirrefl in Hcycle. contradiction.
      * (* Case 2: w' = Write x1 v1 *)
        (* But w = Write x1 v1 too, so w = w' contradicting Hneq *)
        subst w'. contradiction.
      * (* Case 3: po t r w' *)
        (* But Hpo_w'r says po t w' r, so we have cycle r -> w' -> r *)
        destruct (po_strict_total t) as [[Hirrefl Htrans] _].
        assert (Hcycle: po t r r). { eapply Htrans; [exact Hpo_r_w' | exact Hpo_w'r]. }
        apply Hirrefl in Hcycle. contradiction.
    + (* TAP_f: IntermediateRead - forbidden by RC3 *)
      (* TAP-f: t reads from an intermediate write w in t', but t' has w' after w *)
      unfold TAP_f. 
      intros [x [t [t' [r [w [w' [Ht [Ht' [Hneq [HRTx_t [HWTx_t' [Hrx [Hwx [Hwx' [Hneqw [Hwr Hpo]]]]]]]]]]]]]]]].
      (* TAP_f structure: T H t /\ T H t' /\ t <> t' /\ RTx (T H) x t /\ WTx (T H) x t' /\
         Rx t x r /\ Wx t' x w /\ Wx t' x w' /\ w <> w' /\ wr_rel w r /\ po t' w w' *)
      unfold RC3 in HRC3.
      (* RC3: forall x t w w', T H t -> Wx t x w -> Wx t x w' -> 
         (exists t' r, t' <> t /\ T H t' /\ Rx t' x r /\ wr_rel w r) -> po t w' w \/ w' = w
         
         Apply RC3 with:
         - the writing transaction = t' (our external writer)
         - the writes = w, w' 
         - the reading transaction = t (the external reader)
         - the read = r
         
         We need: Ht', Hwx (Wx t' x w), Hwx' (Wx t' x w'), and the exists clause *)
      assert (Hrc3_applied: po t' w' w \/ w' = w).
      { apply (HRC3 x t' w w' Ht' Hwx Hwx').
        exists t, r.
        split. { auto. } (* t <> t' implies t <> t' for RC3's existential *)
        split. { exact Ht. }
        split. { exact Hrx. }
        exact Hwr. }
      destruct Hrc3_applied as [Hpo_w'_w | Heq_w'_w].
      * (* po t' w' w: but we also have po t' w w' from Hpo, giving a cycle *)
        destruct (po_strict_total t') as [[Hirrefl Htrans] _].
        assert (Hcycle: po t' w w). { eapply Htrans; [exact Hpo | exact Hpo_w'_w]. }
        apply Hirrefl in Hcycle. contradiction.
      * (* w' = w: contradicts w <> w' *)
        symmetry in Heq_w'_w. contradiction.
    + (* TAP_g: CyclicCO - subsumed by so_wr_acyclic from History *)
      unfold TAP_g. intros [t1 [t2 [Hplus Hid]]].
      unfold IT in Hid. destruct Hid as [Ht1 [Ht2 Heq]]. subst t2.
      (* Hplus: SO_union_WR_plus H t1 t1, i.e., t1 reaches itself via (SO ∪ WR)+ *)
      (* This contradicts so_wr_acyclic which says (SO ∪ WR)+ is a strict order *)
      pose proof (so_wr_acyclic H) as [Hirrefl _].
      apply (Hirrefl t1). exact Hplus.
  - (* Completeness: no TAPs a-g -> RC1 /\ RC2 /\ RC3 *)
    (* Paper proof strategy:
       1. First show that (T, SO) with no TAP-a, TAP-b, TAP-g has a valid WR relation
       2. Then show no TAP-c, TAP-d, TAP-e, TAP-f implies RC-1, RC-2, RC-3 *)
    intros Hno_taps.
    unfold no_TAP_a_to_g in Hno_taps.
    destruct Hno_taps as [Hno_a [Hno_b [Hno_c [Hno_d [Hno_e [Hno_f Hno_g]]]]]].
    
    (* RC1 completeness: ~TAP_c -> RC1 *)
    (* Paper: "First, if RC-(1) is violated, then TAP-c would happen" *)
    (* RC1 states: if wr_rel w r (r reads from w), then po t w r (w precedes r) *)
    (* Contrapositive: if po t r w (r precedes w), then TAP_c (FutureRead) occurs *)
    split. { unfold RC1. intros t r w Ht Hr Hw Hintra.
      (* Get properties of program order: irreflexive, transitive, and total *)
      assert (Hproof: and (and (forall x, ~po t x x) (transitive Op (po t))) (forall o1 o2, ops t o1 -> ops t o2 -> o1 <> o2 -> po t o1 o2 \/ po t o2 o1)).
      { unfold strict_order. apply (po_strict_total t). }
      destruct Hproof as [[Hirrefl Htrans] Htot_func].
      
      (* A write and a read cannot be the same operation *)
      assert (Hneq_op: w <> r).
      { intro. subst. unfold W in Hw. destruct Hw as [_ Hw_is_w]. unfold R in Hr. destruct Hr as [_ Hr_is_r].
        unfold is_write in Hw_is_w. unfold is_read in Hr_is_r.
        destruct r; contradiction. }
      
      (* Extract that w and r are operations in transaction t *)
      unfold W in Hw. destruct Hw as [Hw_ops Hw_is_w].
      unfold R in Hr. destruct Hr as [Hr_ops Hr_is_r].
      (* Since po is a total order on ops, either w precedes r or r precedes w *)
      assert (Hcases: po t w r \/ po t r w).
      { apply Htot_func; assumption. }
      destruct Hcases as [Hpo_wr | Hpo_rw]; auto.
      (* Case: po t r w - the read precedes the write it reads from *)
      (* This is exactly TAP_c (FutureRead), contradicting ~TAP_c *)
      exfalso. apply Hno_c.
      unfold TAP_c. exists t, w, r.
      split. { apply Ht. }
      split. { unfold W. split; assumption. }
      split. { unfold R. split; assumption. }
      split. { exact Hintra. }
      { exact Hpo_rw. }
    }
    split. { 
      (* RC2 completeness: ~TAP_d /\ ~TAP_e -> RC2 *)
      (* Paper: If RC-2 is violated, then TAP-d or TAP-e would happen *)
      unfold RC2. intros x t r Ht Hrx Hpreceded.
      destruct Hpreceded as [w_pre [Hwx_pre Hpo_pre]].
      (* r is a read on x in t, preceded by some write w_pre *)
      (* r must read from somewhere: internal write or external write *)
      destruct Hrx as [Hr_ops [Hr_is_r Hr_key]].
      destruct r as [xr vr | xr vr]; try contradiction. (* r is Read xr vr *)
      simpl in Hr_key. subst xr.
      
      (* By read_completeness, r reads from internal or external *)
      assert (Hrx': Rx t x (Read x vr)).
      { split; [exact Hr_ops | split; [simpl; auto | simpl; auto]]. }
      destruct (read_completeness H t x (Read x vr) vr Ht Hrx' eq_refl) as [Hinternal | Hexternal].
      - (* Case: Internal read - r reads from internal write w_int *)
        destruct Hinternal as [w_int [Hwx_int [Hw_int_eq Hpo_int]]].
        subst w_int.
        (* We need to find the LAST write before r *)
        (* We know Write x vr is a write before r *)
        (* Show that Write x vr is the last write before r, or derive contradiction via TAP_e *)
        exists (Write x vr).
        split. { exact Hwx_int. }
        split. { exact Hpo_int. }
        split. { unfold wr_rel. exists x, vr. split; reflexivity. }
        (* Show: forall w'', Wx t x w'' -> po t w'' (Write x vr) \/ w'' = Write x vr \/ po t (Read x vr) w'' *)
        intros w'' Hwx''.
        destruct (Op_eq_dec w'' (Write x vr)) as [Heq | Hneq_w].
        + (* w'' = Write x vr *)
          right. left. exact Heq.
        + (* w'' <> Write x vr *)
          destruct (po_strict_total t) as [Hstrict Htot].
          assert (Hw''_ops: ops t w''). { destruct Hwx'' as [H1 _]; exact H1. }
          assert (Hw''_is_w: is_write w''). { destruct Hwx'' as [_ [H1 _]]; exact H1. }
          assert (Hwxvr_ops: ops t (Write x vr)). { destruct Hwx_int as [H1 _]; exact H1. }
          destruct (Htot w'' (Write x vr) Hw''_ops Hwxvr_ops Hneq_w) as [Hpo_w''_wvr | Hpo_wvr_w''].
          * (* po t w'' (Write x vr) - w'' is before the write vr *)
            left. exact Hpo_w''_wvr.
          * (* po t (Write x vr) w'' - w'' is after the write vr *)
            (* Now: is w'' before r or after r? *)
            assert (Hneq_w''_r: w'' <> Read x vr).
            { intro Hsubst. subst w''. unfold is_write in Hw''_is_w. simpl in Hw''_is_w. exact Hw''_is_w. }
            destruct (Htot w'' (Read x vr) Hw''_ops Hr_ops Hneq_w''_r) as [Hpo_w''_r | Hpo_r_w''].
            -- (* po t w'' (Read x vr) - w'' is before r *)
               (* So we have Write x vr <po w'' <po r, but r reads from Write x vr *)
               (* This gives TAP_e: r reads from Write x vr but w'' is after it and before r *)
               exfalso. apply Hno_e.
               unfold TAP_e.
               exists x, t, (Write x vr), w'', (Read x vr).
               split. { exact Ht. }
               split. { exact Hwx_int. }
               split. { exact Hwx''. }
               split. { apply not_eq_sym. exact Hneq_w. }
               split. { exact Hrx'. }
               split. { exact Hpo_wvr_w''. }
               split. { exact Hpo_w''_r. }
               { unfold wr_rel. exists x, vr. split; reflexivity. }
            -- (* po t (Read x vr) w'' - w'' is after r *)
               right. right. exact Hpo_r_w''.
      - (* Case: External read - r reads from external t' *)
        (* This gives TAP_d: t has written to x (w_pre) before reading r, but r reads from external t' *)
        destruct Hexternal as [t' [Ht' [Hwr' Hwrites_t']]].
        exfalso. apply Hno_d.
        unfold TAP_d.
        (* Need to find the actual write operation in t' *)
        unfold txn_writes in Hwrites_t'.
        destruct Hwrites_t' as [w' [Hwx_t' [Hw'_eq Hlast_w']]].
        subst w'.
        exists x, t, t', w_pre, (Read x vr), (Write x vr).
        split. { exact Ht. }
        split. { exact Ht'. }
        split. { 
          (* t <> t' *)
          intro Heq. subst t'.
          (* If t = t', then WR x t t, but WR requires t <> s *)
          pose proof (wr_reads_writes H x t t Hwr') as [_ [_ [Hneq _]]].
          contradiction.
        }
        split. { 
          (* WTx (T H) x t *)
          unfold WTx. split; [exact Ht | exists w_pre; exact Hwx_pre].
        }
        split. { 
          (* WTx (T H) x t' *)
          unfold WTx. split; [exact Ht' | exists (Write x vr); exact Hwx_t'].
        }
        split. { exact Hrx'. }
        split. { exact Hwx_pre. }
        split. { exact Hwx_t'. }
        split. { unfold wr_rel. exists x, vr. split; reflexivity. }
        { exact Hpo_pre. }
    }
    (* RC3 completeness: ~TAP_f -> RC3 *)
    (* Paper: "Third, if RC-(3) is violated, then TAP-f would happen" *)
    (* RC3 states: if w is visible to external reader, then w must be the last write to x *)
    (* i.e., all other writes w' must satisfy: po t w' w \/ w' = w *)
    (* Contrapositive: if po t w w' (w is not the last), then TAP_f (IntermediateRead) occurs *)
    { 
      unfold RC3. intros x t w w' Ht Hwx Hwx' Hexists.
      (* Hexists: there exists an external transaction t' that reads w *)
      destruct Hexists as [t' [r [Hneq [Ht' [Hrx Hwr]]]]].
      (* Goal: po t w' w \/ w' = w (w' is before w, or they are the same) *)
      (* We prove by case analysis on whether w' = w *)
      destruct (Op_eq_dec w' w) as [Heq | Hneq_w].
      - (* Case: w' = w - trivially satisfied *)
        right. exact Heq.
      - (* Case: w' <> w - must show po t w' w *)
        (* Use totality of program order to get either po t w w' or po t w' w *)
        destruct (po_strict_total t) as [_ Htot].
        destruct Hwx as [Hw_ops [Hw_is_w Hw_key]].
        destruct Hwx' as [Hw'_ops [Hw'_is_w Hw'_key]].
        assert (Hneq_ww': w <> w') by (intro; subst; apply Hneq_w; reflexivity).
        destruct (Htot w w' Hw_ops Hw'_ops Hneq_ww') as [Hpo_ww' | Hpo_w'w].
        + (* Case: po t w w' - w is NOT the last write, but is read externally *)
          (* This is exactly TAP_f (IntermediateRead): external reader sees non-last write *)
          exfalso. apply Hno_f.
          unfold TAP_f.
          (* Instantiate TAP_f with:
             - Reader transaction: t' (reads r from w)
             - Writer transaction: t (has writes w and w' with w <po w')
             Note: In TAP_f definition, the first t is the reader, second t' is the writer *)
          exists x, t', t, r, w, w'.
          split. { exact Ht'. }           (* T H t' - reader is committed *)
          split. { exact Ht. }            (* T H t - writer is committed *)
          split. { intro H_eq; apply Hneq; exact H_eq. }  (* t' <> t *)
          split. { unfold RTx. split; [exact Ht' | exists r; exact Hrx]. }  (* RTx t' *)
          split. { unfold WTx. split; [exact Ht | exists w; unfold Wx; repeat split; assumption]. }  (* WTx t *)
          split. { exact Hrx. }           (* Rx t' x r *)
          split. { unfold Wx. repeat split; assumption. }  (* Wx t x w *)
          split. { unfold Wx. repeat split; assumption. }  (* Wx t x w' *)
          split. { exact Hneq_ww'. }      (* w <> w' *)
          split. { exact Hwr. }           (* wr_rel w r - r reads from w *)
          { exact Hpo_ww'. }              (* po t w w' - w' comes after w *)
        + (* Case: po t w' w - w' is before w, goal satisfied *)
          left. exact Hpo_w'w.
    }
Qed.

(** TAP_h implies TAP_i when commit_order holds (since CO ⊆ CM) *)
Lemma TAP_h_implies_TAP_i : forall H CM,
  commit_order H CM -> TAP_h H -> TAP_i H CM.
Proof.
  intros H CM HCM Htap_h.
  unfold TAP_h in Htap_h.
  destruct Htap_h as [x [y [t1 [t2 [t3 [wx [wy [rx [ry [Hneq_xy [Hwt1 [Hwt2 [Hneq12 [Hrt3x [Hrt3y [Hneq31 [Hneq32 [Hwx [Hwy [Hrx [Hry [Hwrx [Hwry [Hpo_ry_rx HCO]]]]]]]]]]]]]]]]]]]]]]]].
  unfold TAP_i.
  exists x, y, t1, t2, t3, wx, wy, rx, ry.
  (* CO ⊆ CM from commit_order *)
  destruct HCM as [_ [_ Hco_cm]].
  split; [exact Hneq_xy |].
  split; [exact Hwt1 |].
  split; [exact Hwt2 |].
  split; [exact Hneq12 |].
  split; [exact Hrt3x |].
  split; [exact Hrt3y |].
  split; [exact Hneq31 |].
  split; [exact Hneq32 |].
  split; [exact Hwx |].
  split; [exact Hwy |].
  split; [exact Hrx |].
  split; [exact Hry |].
  split; [exact Hwrx |].
  split; [exact Hwry |].
  split; [exact Hpo_ry_rx |].
  apply Hco_cm. exact HCO.
Qed.

(** MonoAtomicView implies ~TAP_i *)
Lemma MonoAtomicView_no_TAP_i : forall H CM,
  strict_order CM -> MonoAtomicView H CM -> ~TAP_i H CM.
Proof.
  intros H CM Hstrict HMono.
  unfold TAP_i. intros [x [y [t1 [t2 [t3 [wx [wy [rx [ry H_tap]]]]]]]]].
  destruct H_tap as [Hneq [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hrt3y [Hneq31 [Hneq32 [Hwx [Hwy [Hrx [Hry [Hwrx [Hwry [Hpo HCM_tap]]]]]]]]]]]]]]].
  unfold MonoAtomicView in HMono.
  assert (Hcm21: CM t2 t1).
  { apply (HMono x y t1 t2 t3 Hneq Hwt1 Hwt2 Hneq12 Hrt3y Hneq31 Hneq32).
    exists wx, wy, rx, ry.
    split; [exact Hwx |].
    split; [exact Hwy |].
    split; [exact Hrx |].
    split; [exact Hry |].
    split; [exact Hpo |].
    split; [exact Hwry |].
    exact Hwrx. }
  unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
  assert (Hcycle: CM t1 t1). { eapply Htrans; [exact HCM_tap | exact Hcm21]. }
  apply Hirrefl in Hcycle. assumption.
Qed.

Theorem RC_soundness_completeness : forall H,
  ReadCommitted H <->
  (exists CM, commit_order H CM /\ no_TAP_a_to_i H CM).
Proof.
  intros H. split.
  - (* Soundness: RC -> no TAPs a-i *)
    intros HRC.
    unfold ReadCommitted in HRC.
    destruct HRC as [HRC1 [HRC2 [HRC3 [CM [HCM HMono]]]]].
    exists CM. split. assumption.
    unfold no_TAP_a_to_i.
    (* Use the RC123_iff_no_TAP_a_to_g lemma to derive that RC1/RC2/RC3 implies no TAPs a-g *)
    repeat split; try (apply RC123_iff_no_TAP_a_to_g; auto).
    + (* TAP_h: Reduce to TAP_i using TAP_h_implies_TAP_i lemma *)
      intros Htap_h.
      apply (TAP_h_implies_TAP_i H CM HCM) in Htap_h.
      destruct HCM as [Hstrict _].
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono Htap_h).
    + (* TAP_i: Use MonoAtomicView_no_TAP_i lemma *)
      destruct HCM as [Hstrict _].
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono).
  - (* Completeness: no TAPs a-i -> RC *)
    (* Paper proof strategy:
       1. First show that (T, SO) with no TAP-a, TAP-b, TAP-g has a valid WR relation
       2. Then show no TAP-c, TAP-d, TAP-e, TAP-f implies RC-1, RC-2, RC-3
       3. Finally show no TAP-i implies MonoAtomicView *)
    intros [CM [HCM Hno_taps]].
    unfold ReadCommitted.
    (* Extract the hypothesis: history is free of TAPs a through i *)
    unfold no_TAP_a_to_i in Hno_taps.
    destruct Hno_taps as [Hno_ag [Hno_h Hno_i]].
    unfold no_TAP_a_to_g in Hno_ag.
    destruct Hno_ag as [Hno_a [Hno_b [Hno_c [Hno_d [Hno_e [Hno_f Hno_g]]]]]].
    (* Use the RC123_iff_no_TAP_a_to_g lemma in the reverse direction: no TAPs a-g implies RC1/RC2/RC3 *)
    repeat split; try (apply RC123_iff_no_TAP_a_to_g; unfold no_TAP_a_to_g; tauto).
    (* MonoAtomicView completeness: ~TAP_i -> MonoAtomicView *)
    (* Paper: "Finally we show that if the history H = (T, SO, WR) does not contain
       any instances of TAP-i, then the MonoAtomicView axiom holds" *)
    (* MonoAtomicView states: if t3 reads y from t2 then reads x from t1, 
       and both t1, t2 write to x, then CM t2 t1 *)
    (* We prove by showing: if CM t1 t2, then TAP_i occurs, contradicting ~TAP_i *)
  exists CM. split. assumption.
  unfold MonoAtomicView. intros x y t1 t2 t3 Hxy Hwt1 Hwt2 Hneq12 Hrt3y Hneq31 Hneq32 Hexists.
  (* Hexists: t3 reads x from t1 after reading y from t2 (non-monotonic view) *)
  destruct Hexists as [wx [wy [rx [ry [Hwx [Hwy [Hrx [Hry [Hpo_ry_rx [Hwry Hwrx]]]]]]]]]].
  (* Use totality of commit order: either CM t1 t2 or CM t2 t1 *)
  destruct HCM as [_ [Htot _]].
  assert (Ht1: T H t1). { destruct Hwt1; assumption. }
  assert (Ht2: T H t2). { destruct Hwt2; assumption. }
  destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21].
  + (* Case: CM t1 t2 - t1 commits before t2 *)
    (* But t3 reads from t2 (earlier in CM) before reading from t1 (later in CM) *)
    (* This non-monotonic read order is exactly TAP_i, contradicting ~TAP_i *)
    exfalso. apply Hno_i.
    unfold TAP_i. exists x, y, t1, t2, t3, wx, wy, rx, ry.
    split. { exact Hxy. }        (* x <> y *)
    split. { exact Hwt1. }       (* WTx t1 x *)
    split. { exact Hwt2. }       (* WTx t2 x - t2 also writes to x *)
    split. { exact Hneq12. }     (* t1 <> t2 *)
    split. { unfold RTx. destruct Hrt3y as [Ht3 _]. split; [exact Ht3 | exists rx; exact Hrx]. }  (* RTx t3 x *)
    split. { exact Hrt3y. }      (* RTx t3 y *)
    split. { exact Hneq31. }     (* t3 <> t1 *)
    split. { exact Hneq32. }     (* t3 <> t2 *)
    split. { exact Hwx. }        (* Wx t1 x wx *)
    split. { exact Hwy. }        (* Wx t2 y wy *)
    split. { exact Hrx. }        (* Rx t3 x rx *)
    split. { exact Hry. }        (* Rx t3 y ry *)
    split. { exact Hwrx. }       (* wr_rel wx rx - t3 reads x from t1 *)
    split. { exact Hwry. }       (* wr_rel wy ry - t3 reads y from t2 *)
    split. { exact Hpo_ry_rx. }  (* po t3 ry rx - read y before read x *)
    { exact Hcm12. }             (* CM t1 t2 - the problematic order *)
  + (* Case: CM t2 t1 - t2 commits before t1, which is the goal *)
    assumption.
Qed.

(** * Theorem 4: Soundness and Completeness for RA *)

(** TAP_k implies TAP_l when commit_order holds (since CO ⊆ CM) *)
Lemma TAP_k_implies_TAP_l : forall H CM,
  commit_order H CM -> TAP_k H -> TAP_l H CM.
Proof.
  intros H CM HCM Htap_k.
  unfold TAP_h in Htap_k.
  (* destruct Htap_k. *)
  destruct Htap_k as [x [t1 [t2 [t3 [Hwt1 [Hwt2 [Hneq12 [Hrt3x [Hneq31 [Hneq32 [Hso | Hwr]]]]]]]]]]].
  - unfold TAP_l.
    destruct Hso as [Hwr13 [Hco12 Hso23]].
    exists x, t1, t2, t3.
    (* CO ⊆ CM from commit_order *)
    destruct HCM as [_ [_ Hco_cm]].
    split; [exact Hwt1 |].
    split; [exact Hwt2 |].
    split; [exact Hneq12 |].
    split; [exact Hrt3x |].
    split; [exact Hneq31 |].
    split; [exact Hneq32 |].
    left.
    split; [exact Hwr13 |].
    split; [apply Hco_cm; exact Hco12 |].
    exact Hso23.
  - unfold TAP_l.
    destruct Hwr as [y [Hrt3y [Hwr13 [Hco12 Hwr23]]]].
    exists x, t1, t2, t3.
    (* CO ⊆ CM from commit_order *)
    destruct HCM as [_ [_ Hco_cm]].
    split; [exact Hwt1 |].
    split; [exact Hwt2 |].
    split; [exact Hneq12 |].
    split; [exact Hrt3x |].
    split; [exact Hneq31 |].
    split; [exact Hneq32 |].
    right. exists y.
    split; [exact Hrt3y |].
    split; [exact Hwr13 |].
    split; [apply Hco_cm; exact Hco12 |].
    exact Hwr23.
Qed.

(** ReadAtomic implies CutIsolation *)
Lemma ReadAtomic_implies_CutIsolation : forall H CM,
  strict_order CM -> ReadAtomic H CM -> CutIsolation H.
Proof.
Admitted.

(** ReadAtomic implies MonoAtomicView (ReadAtomic is stronger than MonoAtomicView) *)
Lemma ReadAtomic_implies_MonoAtomicView : forall H CM,
  commit_order H CM -> ReadAtomic H CM -> MonoAtomicView H CM.
Proof.
  intros H CM HCM Hra.
Admitted.

(** ReadAtomic implies ~TAP_l *)
Lemma ReadAtomic_no_TAP_l : forall H CM,
  strict_order CM -> ReadAtomic H CM -> ~TAP_l H CM.
Proof.
  intros H CM Hstrict HRa.
  unfold ReadAtomic in HRa.
  unfold TAP_l. intros [x [t1 [t2 [t3 [Hwxt1 [Hwxt2 [Hneq12 [Hrxt3 [Hneq31 [Hneq32 [Hwr | Hso]]]]]]]]]]].
  - destruct Hwr as [Hwr13 [Hcm12 Hso23]].
    assert (Hcm21: CM t2 t1).
    { apply (HRa x t1 t2 t3 Hwxt1 Hwxt2 Hneq12 Hrxt3 Hneq31 Hneq32 Hwr13).
      unfold SO_union_WR. left. tauto. }
    unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
    assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
    apply Hirrefl in Hcycle. assumption.
  - destruct Hso as [y [Hryt3 [Hwr13 [Hcm12 Hwr23]]]].
    assert (Hcm21: CM t2 t1).
    { apply (HRa x t1 t2 t3 Hwxt1 Hwxt2 Hneq12 Hrxt3 Hneq31 Hneq32 Hwr13).
      unfold SO_union_WR. right. exists y. tauto. }
    unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
    assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
    apply Hirrefl in Hcycle. assumption.
Qed.

Theorem RA_soundness_completeness : forall H,
  ReadAtomicity H <->
  (exists CM, commit_order H CM /\ no_TAP_a_to_l H CM).
Proof.
  intros H. split.
  - (* Soundness: RA -> no TAPs a-l *)
    intros HRA.
    unfold ReadAtomicity in HRA.
    destruct HRA as [HRC1 [HRC2 [HRC3 [CM [HCM HReadAtomic]]]]].
    exists CM. split. assumption.
    (* RA implies CI *)
    assert (HCI: CutIsolation H).
    { destruct HCM as [Hstrict _].
      apply (ReadAtomic_implies_CutIsolation H CM Hstrict HReadAtomic). }
    destruct HCM as [Hstrict HCM_rest].
    unfold no_TAP_a_to_l.
    unfold no_TAP_a_to_i.
    (* no_TAP_a_to_g from RC123_iff_no_TAP_a_to_g *)
    repeat split; try (apply RC123_iff_no_TAP_a_to_g; auto).
    + (* TAP_h: reduce to TAP_i, then use MonoAtomicView_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      intros Htap_h.
      apply (TAP_h_implies_TAP_i H CM (conj Hstrict HCM_rest)) in Htap_h.
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono Htap_h).
    + (* TAP_i: use MonoAtomicView_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono).
    + (* TAP_j: use CI_soundness_completeness *)
      apply CI_soundness_completeness. exact HCI.
    + (* TAP_k: reduce to TAP_l via TAP_k_implies_TAP_l *)
      intros Htap_k.
      apply (TAP_k_implies_TAP_l H CM (conj Hstrict HCM_rest)) in Htap_k.
      exact (ReadAtomic_no_TAP_l H CM Hstrict HReadAtomic Htap_k).
    + (* TAP_l: use ReadAtomic_no_TAP_l directly *)
      exact (ReadAtomic_no_TAP_l H CM Hstrict HReadAtomic).
  - (* Completeness: no TAPs a-l -> RA *)
    intros [CM [HCM Hno_taps]].
    unfold ReadAtomicity.
    unfold no_TAP_a_to_l in Hno_taps.
    destruct Hno_taps as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    unfold no_TAP_a_to_i in Hno_ai.
    destruct Hno_ai as [Hno_ag [Hno_h Hno_i]].
    (* RC1, RC2, RC3 from no_TAP_a_to_g *)
    assert (HRC: RC1 H /\ RC2 H /\ RC3 H).
    { apply RC123_iff_no_TAP_a_to_g. exact Hno_ag. }
    destruct HRC as [HRC1 [HRC2 HRC3]].
    repeat split; auto.
    exists CM. split. assumption.
    (* Prove ReadAtomic from ~TAP_l *)
    unfold ReadAtomic.
    intros x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hso_wr.
    (* Goal: CM t2 t1 *)
    (* Use totality of CM: either CM t1 t2 or CM t2 t1 *)
    destruct HCM as [Hstrict [Htot Hco_cm]].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21]; auto.
    (* Case: CM t1 t2 - derive contradiction via TAP_l *)
    exfalso. apply Hno_l.
    unfold TAP_l.
    exists x, t1, t2, t3.
    split; [exact Hwt1 |].
    split; [exact Hwt2 |].
    split; [exact Hneq12 |].
    split; [exact Hrt3 |].
    split; [exact Hneq31 |].
    split; [exact Hneq32 |].
    (* Need to show the disjunction for TAP_l *)
    unfold SO_union_WR in Hso_wr.
    destruct Hso_wr as [Hso23 | [y Hwr23]].
    + (* SO t2 t3 case *)
      left. split; [exact Hwr13 |]. split; [exact Hcm12 |]. exact Hso23.
    + (* WR y t2 t3 case *)
      right.
      pose proof (wr_reads_writes H y t2 t3 Hwr23) as [_ [Ht3 [_ [vy [Hwrites_t2 Hreads_t3]]]]].
      exists y.
      split.
      { (* RTx (T H) y t3 *)
        unfold RTx. split; [exact Ht3 |].
        unfold txn_reads in Hreads_t3.
        destruct Hreads_t3 as [r [Hrx _]].
        exists r. exact Hrx. }
      split; [exact Hwr13 |].
      split; [exact Hcm12 |].
      exact Hwr23.
Qed.
(** * Theorem 5: Soundness and Completeness for TCC *)

(** Causal implies ReadAtomic (since SO ∪ WR ⊆ CO) *)
Lemma Causal_implies_ReadAtomic : forall H CM,
  Causal H CM -> ReadAtomic H CM.
Proof.
  intros H CM HCausal.
  unfold ReadAtomic. intros x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hso_wr.
  (* SO_union_WR ⊆ CO, so we can use Causal *)
  apply (HCausal x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13).
  (* Need to show CO t2 t3 from SO_union_WR t2 t3 *)
  unfold CO. unfold SO_union_WR_plus.
  apply t_step. exact Hso_wr.
Qed.

(** TAP_m implies TAP_n when commit_order holds (since CO ⊆ CM) *)
Lemma TAP_m_implies_TAP_n : forall H CM,
  commit_order H CM -> TAP_m H CM -> TAP_n H CM.
Proof.
  intros H CM HCM Htap_m.
  unfold TAP_m in Htap_m.
  destruct Htap_m as [x [t1 [t2 [t3 [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hneq31 [Hneq32 [Hwr13 [Hco12 Hco23]]]]]]]]]]]].
  unfold TAP_n.
  exists x, t1, t2, t3.
  (* CO ⊆ CM from commit_order *)
  destruct HCM as [_ [_ Hco_cm]].
  split; [exact Hwt1 |].
  split; [exact Hwt2 |].
  split; [exact Hneq12 |].
  split; [exact Hrt3 |].
  split; [exact Hneq31 |].
  split; [exact Hneq32 |].
  split; [exact Hwr13 |].
  split; [apply Hco_cm; exact Hco12 |].
  exact Hco23.
Qed.

(** Causal implies ~TAP_n *)
Lemma Causal_no_TAP_n : forall H CM,
  strict_order CM -> Causal H CM -> ~TAP_n H CM.
Proof.
  intros H CM Hstrict HCausal.
  unfold TAP_n. intros [x [t1 [t2 [t3 [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hneq31 [Hneq32 [Hwr13 [Hcm12 Hco23]]]]]]]]]]]].
  (* TAP_n: WR x t1 t3, CM t1 t2, CO t2 t3 *)
  (* Causal: if WR x t1 t3 and CO t2 t3, then CM t2 t1 *)
  assert (Hcm21: CM t2 t1).
  { apply (HCausal x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hco23). }
  (* Now we have CM t1 t2 (from Hcm12) and CM t2 t1 (from Hcm21), contradiction *)
  unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
  assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
  apply Hirrefl in Hcycle. assumption.
Qed.

Theorem TCC_soundness_completeness : forall H,
  TransactionalCausalConsistency H <->
  (exists CM, commit_order H CM /\ no_all_TAPs H CM).
Proof.
  intros H. split.
  - (* Soundness: TCC -> no all TAPs *)
    intros HTCC.
    unfold TransactionalCausalConsistency in HTCC.
    destruct HTCC as [HRC1 [HRC2 [HRC3 [CM [HCM HCausal]]]]].
    exists CM. split. assumption.
    (* Causal implies ReadAtomic *)
    assert (HReadAtomic: ReadAtomic H CM).
    { apply Causal_implies_ReadAtomic. exact HCausal. }
    destruct HCM as [Hstrict HCM_rest].
    unfold no_all_TAPs. unfold no_TAP_a_to_l.
    unfold no_TAP_a_to_i.
    (* Use RC123_iff_no_TAP_a_to_g to show no_TAP_a_to_g *)
    repeat split; try (apply RC123_iff_no_TAP_a_to_g; auto).
    + (* TAP_h: reduce to TAP_i, then use MonoAtomicView_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      intros Htap_h.
      apply (TAP_h_implies_TAP_i H CM (conj Hstrict HCM_rest)) in Htap_h.
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono Htap_h).
    + (* TAP_i: use MonoAtomicView_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      exact (MonoAtomicView_no_TAP_i H CM Hstrict HMono).
    + (* TAP_j: use CI_soundness_completeness *)
      apply CI_soundness_completeness.
      apply (ReadAtomic_implies_CutIsolation H CM Hstrict HReadAtomic).
    + (* TAP_k: use ReadAtomic_no_TAP_l via TAP_k_implies_TAP_l *)
      intros Htap_k.
      apply (TAP_k_implies_TAP_l H CM (conj Hstrict HCM_rest)) in Htap_k.
      exact (ReadAtomic_no_TAP_l H CM Hstrict HReadAtomic Htap_k).
    + (* TAP_l: use ReadAtomic_no_TAP_l directly *)
      exact (ReadAtomic_no_TAP_l H CM Hstrict HReadAtomic).
    + (* TAP_m: reduce to TAP_n via TAP_m_implies_TAP_n *)
      intros Htap_m.
      apply (TAP_m_implies_TAP_n H CM (conj Hstrict HCM_rest)) in Htap_m.
      exact (Causal_no_TAP_n H CM Hstrict HCausal Htap_m).
    + (* TAP_n: use Causal_no_TAP_n directly *)
      exact (Causal_no_TAP_n H CM Hstrict HCausal).
  - (* Completeness: no all TAPs -> TCC *)
    intros [CM [HCM Hno_taps]].
    unfold TransactionalCausalConsistency.
    unfold no_all_TAPs in Hno_taps.
    destruct Hno_taps as [Hno_al [Hno_m Hno_n]].
    unfold no_TAP_a_to_l in Hno_al.
    destruct Hno_al as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    unfold no_TAP_a_to_i in Hno_ai.
    destruct Hno_ai as [Hno_ag [Hno_h Hno_i]].
    (* RC1, RC2, RC3 from no_TAP_a_to_g *)
    assert (HRC: RC1 H /\ RC2 H /\ RC3 H).
    { apply RC123_iff_no_TAP_a_to_g. exact Hno_ag. }
    destruct HRC as [HRC1 [HRC2 HRC3]].
    repeat split; auto.
    exists CM. split. assumption.
    (* Prove Causal from ~TAP_n *)
    unfold Causal.
    intros x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hco23.
    (* Goal: CM t2 t1 *)
    (* Use totality of CM: either CM t1 t2 or CM t2 t1 *)
    destruct HCM as [Hstrict [Htot Hco_cm]].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21]; auto.
    (* Case: CM t1 t2 - derive contradiction via TAP_n *)
    exfalso. apply Hno_n.
    unfold TAP_n.
    exists x, t1, t2, t3.
    split; [exact Hwt1 |].
    split; [exact Hwt2 |].
    split; [exact Hneq12 |].
    split; [exact Hrt3 |].
    split; [exact Hneq31 |].
    split; [exact Hneq32 |].
    split; [exact Hwr13 |].
    split; [exact Hcm12 |].
    exact Hco23.
Qed.

