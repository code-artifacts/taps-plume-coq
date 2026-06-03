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
Parameter OpId : Type.
Parameter OpId_eq_dec : forall (o1 o2 : OpId), {o1 = o2} + {o1 <> o2}.

Inductive Op : Type :=
  | Read (op_id : OpId) (x : Key) (v : Value) : Op
  | Write (op_id : OpId) (x : Key) (v : Value) : Op.

Arguments Read {_} _ _.
Arguments Write {_} _ _.

(** Extract operation identity *)
Definition op_id (o : Op) : OpId :=
  match o with
  | @Read oid _ _ => oid
  | @Write oid _ _ => oid
  end.

Definition Op_eq_dec : forall (o1 o2 : Op), {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality; auto using OpId_eq_dec, Key_eq_dec, Value_eq_dec.
Defined.

(** Extract key from an operation *)
Definition op_key (o : Op) : Key :=
  match o with
  | @Read _ x _ => x
  | @Write _ x _ => x
  end.

(** Extract value from an operation *)
Definition op_value (o : Op) : Value :=
  match o with
  | @Read _ _ v => v
  | @Write _ _ v => v
  end.

(** Check if operation is a read *)
Definition is_read (o : Op) : Prop :=
  match o with
  | @Read _ _ _ => True
  | @Write _ _ _ => False
  end.

(** Check if operation is a write *)
Definition is_write (o : Op) : Prop :=
  match o with
  | @Read _ _ _ => False
  | @Write _ _ _ => True
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
  exists w, Wx t x w /\ op_value w = v /\
  forall w', Wx t x w' -> po t w' w \/ w' = w.

(** Transaction reads value v from key x (first read before any write) *)
Definition txn_reads (t : Transaction) (x : Key) (v : Value) : Prop :=
  exists r, Rx t x r /\ op_value r = v /\
  (forall w, Wx t x w -> ~po t w r) /\
  (forall r', Rx t x r' -> po t r r' \/ r' = r).

(** Notation: t ⊢ W(x, v) *)
Notation "t '⊢' 'W(' x ',' v ')'" := (txn_writes t x v) (at level 80).

(** Notation: t ⊢ R(x, v) *)
Notation "t '⊢' 'R(' x ',' v ')'" := (txn_reads t x v) (at level 80).

(** General operation write-read relation *)
Definition wr_rel : relation Op :=
  fun w r => is_write w /\ is_read r /\
    op_key w = op_key r /\ op_value w = op_value r.

Notation "w '−wr→' r" := (wr_rel _ w r) (at level 70).

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

  (** Assumption 2: Unique values.
      Every written key/value pair identifies a unique write operation,
      including writes in aborted transactions. *)
  unique_values : forall t1 t2 x v,
    (T t1 \/ Taborted t1) -> (T t2 \/ Taborted t2) ->
    forall w1 w2,
    Wx t1 x w1 -> op_value w1 = v ->
    Wx t2 x w2 -> op_value w2 = v ->
    w1 = w2;
  
  (** WR constraints *)
  wr_unique : forall t x r,
    T t -> Rx t x r ->
    exists! w, exists ts, T ts /\ Wx ts x w /\ wr_rel w r;

  (** (SO U WR) is acyclic**)
  so_wr_acyclic : strict_order (clos_trans Transaction (fun t1 t2 => SO t1 t2 \/ exists x, WR x t1 t2));

  (** Additional Well-formedness Axioms, not included in the paper *)
  
  (** Disjointness of Committed and Aborted Transactions *)
  disjoint_T_Taborted : forall t, T t -> ~Taborted t;
    
  (** Operations belong to unique transactions. *)
  op_txn_unique : forall t1 t2 o,
    ops t1 o -> ops t2 o -> t1 = t2;

  (** Operation-level write/read facts iff transaction-level WR. *)
  wr_iff_WR : forall x t s,
    WR x t s <->
      T t /\ T s /\ t <> s /\
      exists w r,
        Wx t x w /\ Rx s x r /\ wr_rel w r
}.

(** Consequences of the History well-formedness assumptions. *)

Lemma read_has_committed_source : forall H t x r,
  T H t ->
  Rx t x r ->
  exists ts w, T H ts /\ Wx ts x w /\ wr_rel w r.
Proof.
  intros H t x r Ht Hrx.
  destruct (wr_unique H t x r Ht Hrx) as [w [[ts [Hts [Hwx Hwr]]] _]].
  exists ts, w. exact (conj Hts (conj Hwx Hwr)).
Qed.

Lemma wr_implies_WR : forall H t s w r,
  T H t ->
  T H s ->
  t <> s ->
  ops t w ->
  ops s r ->
  wr_rel w r ->
  WR H (op_key w) t s.
Proof.
  intros H t s w r Ht Hs Hneq Hw_ops Hr_ops Hwr.
  apply (proj2 (wr_iff_WR H (op_key w) t s)).
  destruct Hwr as [Hw_is_w [Hr_is_r [Hkey Hvalue]]].
  repeat split; auto.
  exists w, r.
  split.
  - split; [exact Hw_ops | split; [exact Hw_is_w | reflexivity]].
  - split.
    + split; [exact Hr_ops | split; [exact Hr_is_r | symmetry; exact Hkey]].
    + split; [exact Hw_is_w | split; [exact Hr_is_r | split; [exact Hkey | exact Hvalue]]].
Qed.

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

(** * Definition 3: Cut Isolation *)

Definition CutIsolation (H : History) : Prop :=
  forall x v v' t t1 t2 r1 r2 w1 w2,
    RTx (T H) x t ->
    WTx (T H) x t1 -> t1 <> t ->
    WTx (T H) x t2 -> t2 <> t ->
    Rx t x r1 -> op_value r1 = v ->
    Rx t x r2 -> op_value r2 = v' ->
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
    Rx t x r1 /\ op_value r1 = v /\
    Rx t x r2 /\ op_value r2 = v' /\
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
    destruct Hconj as
      [Hneqv [Hneq1 [Hneq2 [Hrt [Hwt1 [Hwt2 [Hr1 [Heqr1 [Hr2 [Heqr2 [Hw1 [Hw2 [Hneq12 [Hwr1 Hwr2]]]]]]]]]]]]]].
    assert (v = v').
    { apply (HCI x v v' t t1 t2 r1 r2 w1 w2); auto.
      intro H_eq.
      subst r2.
      rewrite Heqr1 in Heqr2.
      exact (Hneqv Heqr2).
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
    destruct Hr1 as [Hr1_ops [Hr1_read Hr1_key]].
    destruct Hr2 as [Hr2_ops [Hr2_read Hr2_key]].
    destruct Hw1 as [Hw1_ops [Hw1_write Hw1_key]].
    destruct Hw2 as [Hw2_ops [Hw2_write Hw2_key]].
    destruct Hwr1 as [Hwr1_write [Hwr1_read [Hwr1_key Hwr1_value]]].
    destruct Hwr2 as [Hwr2_write [Hwr2_read [Hwr2_key Hwr2_value]]].
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
    + (* TAP_a: ThinAirRead - subsumed by Definition 2 (wr_unique) *)
      unfold TAP_a. intros [r [t [Ht [Hr Hno_write]]]].
      destruct Hr as [Hops Hr_is_r].
      assert (Hrx: Rx t (op_key r) r).
      { repeat split; auto. }
      destruct (read_has_committed_source H t (op_key r) r Ht Hrx)
        as [ts [w [Hts [Hwx Hwr]]]].
      pose proof (Hno_write w ts) as Hnot.
      apply Hnot.
      split.
      * left. exact Hts.
      * unfold W. destruct Hwx as [Hwx_ops [Hw_is_w _]].
        split; assumption.
      * exact Hwr.
    + (* TAP_b: AbortedRead - subsumed by Definition 2 (disjoint_T_Taborted, unique_values, op_txn_unique) *)
      unfold TAP_b. intros [r [w [t [ta [Ht [Hr [Hta [Hw Hwr]]]]]]]].
      destruct Hwr as [Hwr_write [Hwr_read [Hwr_key Hwr_value]]].
      destruct Hr as [Hr_ops Hr_is_r].
      assert (Hrx: Rx t (op_key w) r).
      { split; [exact Hr_ops | split; [exact Hr_is_r | symmetry; exact Hwr_key]]. }
      destruct (read_has_committed_source H t (op_key w) r Ht Hrx)
        as [ts [w' [Hts [Hwx' Hwr']]]].
      destruct Hw as [Hops_ta Hw_is_w].
      assert (Hwx_aborted: Wx ta (op_key w) w).
      { split; [exact Hops_ta | split; [exact Hw_is_w | reflexivity]]. }
      destruct Hwr' as [_ [_ [_ Hwr'_value]]].
      assert (Heq_w: w' = w).
      { apply (unique_values H ts ta (op_key w) (op_value r)
          (or_introl Hts) (or_intror Hta) w' w).
        - exact Hwx'.
        - exact Hwr'_value.
        - exact Hwx_aborted.
        - exact Hwr_value. }
      subst w'.
      destruct Hwx' as [Hops_ts _].
      assert (Heq_ts_ta: ts = ta) by
        exact (op_txn_unique H ts ta w Hops_ts Hops_ta).
      subst ta. apply (disjoint_T_Taborted H ts); assumption.
    + (* TAP_c *) unfold TAP_c. intros [t [w [r [Ht [Hw [Hr [Hwr Hpo]]]]]]].
      unfold RC1 in HRC1.
      (* By RC1, if wr_rel w r, then po t w r *)
      specialize (HRC1 t r w Ht Hr Hw Hwr).
      (* Now we have po t w r from RC1, but Hpo says po t r w. *)
      destruct (po_strict_total t) as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      assert (Cycle: po t w w). { eapply Htrans; eassumption. }
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
      destruct Hwr_int as [_ [_ [Hkey_int Hval_int]]].
      destruct Hwr as [_ [_ [Hkey_ext Hval_ext]]].
      destruct Hwx_int as [Hwx_int_ops [Hwx_int_write Hwx_int_key]].
      destruct Hwx' as [Hwx'_ops [Hwx'_write Hwx'_key]].
      assert (Heq_w: w_int = w').
      { apply (unique_values H t t' x (op_value r)
          (or_introl Ht) (or_introl Ht') w_int w').
        - repeat split; auto.
        - exact Hval_int.
        - repeat split; auto.
        - exact Hval_ext. }
      subst w_int.
      assert (Heq_t_t': t = t') by
        exact (op_txn_unique H t t' w' Hwx_int_ops Hwx'_ops).
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
      specialize (Hmax w' Hwx').
      destruct Hmax as [Hpo_w'_wlast | [Heq_w'_wlast | Hpo_r_w']].
      * (* Case 1: po t w' w_last *)
        (* But Hpo_ww' says po t w w', and w = w_last by op uniqueness. *)
        assert (Heq_w_wlast: w = w_last).
        { destruct Hwr as [_ [_ [_ Hval_w]]].
          destruct Hwr_last as [_ [_ [_ Hval_last]]].
          apply (unique_values H t t x (op_value r)
            (or_introl Ht) (or_introl Ht) w w_last); auto. }
        subst w_last.
        destruct (po_strict_total t) as [[Hirrefl Htrans] _].
        assert (Hcycle: po t w w).
        { eapply Htrans; [exact Hpo_ww' | exact Hpo_w'_wlast]. }
        apply Hirrefl in Hcycle. contradiction.
      * (* Case 2: w' = w_last *)
        assert (Heq_w_wlast: w = w_last).
        { destruct Hwr as [_ [_ [_ Hval_w]]].
          destruct Hwr_last as [_ [_ [_ Hval_last]]].
          apply (unique_values H t t x (op_value r)
            (or_introl Ht) (or_introl Ht) w w_last); auto. }
        subst w_last. subst w'. contradiction.
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
      unfold RC2. intros x t r Ht Hrx [w_pre [Hwx_pre Hpo_pre]].
      destruct (read_has_committed_source H t x r Ht Hrx)
        as [ts [w_src [Hts [Hwx_src Hwr_src]]]].
      destruct (classic (ts = t)) as [Heq_ts | Hneq_ts].
      - (* Internal source *)
        subst ts.
        destruct Hwx_src as [Hw_src_ops [Hw_src_is_w Hw_src_key]].
        destruct Hrx as [Hr_ops [Hr_is_r Hr_key]].
        assert (Hneq_src_r: w_src <> r).
        { intro Heq. subst w_src. destruct r; contradiction. }
        destruct (po_strict_total t) as [_ Htot].
        assert (Hpo_src_r: po t w_src r).
        { destruct (Htot w_src r Hw_src_ops Hr_ops Hneq_src_r) as [Hpo | Hpo]; auto.
          exfalso. apply Hno_c.
          unfold TAP_c. exists t, w_src, r.
          split; [exact Ht |].
          split; [unfold W; split; assumption |].
          split; [unfold R; split; assumption |].
          split; [exact Hwr_src | exact Hpo]. }
        exists w_src.
        split. { repeat split; assumption. }
        split. { exact Hpo_src_r. }
        split. { exact Hwr_src. }
        intros w'' Hwx''.
        destruct (Op_eq_dec w'' w_src) as [Heq | Hneq_w''].
        { subst w''. tauto. }
        destruct Hwx'' as [Hw''_ops [Hw''_is_w Hw''_key]].
        destruct (Htot w'' w_src Hw''_ops Hw_src_ops Hneq_w'')
          as [Hpo_w''_src | Hpo_src_w''].
        { left. exact Hpo_w''_src. }
        assert (Hneq_w''_r: w'' <> r).
        { intro Heq. subst w''. destruct r; contradiction. }
        destruct (Htot w'' r Hw''_ops Hr_ops Hneq_w''_r)
          as [Hpo_w''_r | Hpo_r_w''].
        + exfalso. apply Hno_e.
          unfold TAP_e. exists x, t, w_src, w'', r.
          split; [exact Ht |].
          split; [split; [exact Hw_src_ops | split; [exact Hw_src_is_w | exact Hw_src_key]] |].
          split; [split; [exact Hw''_ops | split; [exact Hw''_is_w | exact Hw''_key]] |].
          split; [intro Heq; apply Hneq_w''; symmetry; exact Heq |].
          split; [split; [exact Hr_ops | split; [exact Hr_is_r | exact Hr_key]] |].
          split; [exact Hpo_src_w'' |].
          split; [exact Hpo_w''_r | exact Hwr_src].
        + right. right. exact Hpo_r_w''.
      - (* External source, while t has a previous write to x: TAP_d *)
        exfalso. apply Hno_d.
        unfold TAP_d. exists x, t, ts, w_pre, r, w_src.
        exact (conj Ht
          (conj Hts
            (conj (fun Heq => Hneq_ts (eq_sym Heq))
              (conj (conj Ht (ex_intro _ w_pre Hwx_pre))
                (conj (conj Hts (ex_intro _ w_src Hwx_src))
                  (conj Hrx
                    (conj Hwx_pre
                      (conj Hwx_src
                        (conj Hwr_src Hpo_pre))))))))).
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
  intros H CM [_ [_ Hco_cm]] Htap_h.
  destruct Htap_h as [x [y [t1 [t2 [t3 [wx [wy [rx [ry H_tap]]]]]]]]].
  exists x, y, t1, t2, t3, wx, wy, rx, ry.
  destruct H_tap as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? HCO]]]]]]]]]]]]]]].
  repeat (split; [assumption |]).
  apply Hco_cm; exact HCO.
Qed.

(** MonoAtomicView <-> ~TAP_i *)
Lemma MonoAtomicView_iff_no_TAP_i : forall H CM,
  commit_order H CM -> (MonoAtomicView H CM <-> ~TAP_i H CM).
Proof.
  intros H CM HCM. split.
  - (* Soundness: MonoAtomicView -> ~TAP_i *)
    intros HMono.
    unfold TAP_i. intros [x [y [t1 [t2 [t3 [wx [wy [rx [ry H_tap]]]]]]]]].
    destruct H_tap as [Hneq [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hrt3y [Hneq31 [Hneq32 [Hwx [Hwy [Hrx [Hry [Hwrx [Hwry [Hpo HCM_tap]]]]]]]]]]]]]]].
    unfold MonoAtomicView in HMono.
    assert (Hcm21: CM t2 t1).
    { apply (HMono x y t1 t2 t3 Hneq Hwt1 Hwt2 Hneq12 Hrt3y Hneq31 Hneq32).
      exists wx, wy, rx, ry.
      repeat (split; [assumption |]).
      exact Hwrx. }
    destruct HCM as [Hstrict _].
    unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
    assert (Hcycle: CM t1 t1). { eapply Htrans; [exact HCM_tap | exact Hcm21]. }
    apply Hirrefl in Hcycle. assumption.
  - (* Completeness: ~TAP_i -> MonoAtomicView *)
    (* Paper: "Finally we show that if the history H = (T, SO, WR) does not contain
       any instances of TAP-i, then the MonoAtomicView axiom holds" *)
    intros Hno_i.
    unfold MonoAtomicView. intros x y t1 t2 t3 Hxy Hwt1 Hwt2 Hneq12 Hrt3y Hneq31 Hneq32 Hexists.
    destruct Hexists as [wx [wy [rx [ry [Hwx [Hwy [Hrx [Hry [Hpo_ry_rx [Hwry Hwrx]]]]]]]]]].
    (* Use totality of commit order: either CM t1 t2 or CM t2 t1 *)
    destruct HCM as [_ [Htot _]].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21].
    + (* Case: CM t1 t2 - contradicts ~TAP_i *)
      exfalso. apply Hno_i.
      unfold TAP_i. exists x, y, t1, t2, t3, wx, wy, rx, ry.
      repeat (split; [assumption |]).
      split. { unfold RTx. destruct Hrt3y as [Ht3 _]. split; [exact Ht3 | exists rx; exact Hrx]. }
      repeat (split; [assumption |]).
      { exact Hcm12. }
    + (* Case: CM t2 t1 - which is the goal *)
      assumption.
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
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM HCM) HMono Htap_h).
    + (* TAP_i: Use MonoAtomicView_iff_no_TAP_i lemma *)
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM HCM) HMono).
  - (* Completeness: no TAPs a-i -> RC *)
    intros [CM [HCM Hno_taps]].
    unfold ReadCommitted.
    unfold no_TAP_a_to_i in Hno_taps.
    destruct Hno_taps as [Hno_ag [Hno_h Hno_i]].
    unfold no_TAP_a_to_g in Hno_ag.
    destruct Hno_ag as [Hno_a [Hno_b [Hno_c [Hno_d [Hno_e [Hno_f Hno_g]]]]]].
    repeat split; try (apply RC123_iff_no_TAP_a_to_g; unfold no_TAP_a_to_g; tauto).
    (* ~TAP_i -> MonoAtomicView via MonoAtomicView_iff_no_TAP_i *)
    exists CM. split. assumption.
    apply (proj2 (MonoAtomicView_iff_no_TAP_i H CM HCM)). exact Hno_i.
Qed.

(** * Theorem 4: Soundness and Completeness for RA *)

(** TAP_k implies TAP_l when commit_order holds (since CO ⊆ CM) *)
Lemma TAP_k_implies_TAP_l : forall H CM,
  commit_order H CM -> TAP_k H -> TAP_l H CM.
Proof.
  intros H CM [_ [_ Hco_cm]] [x [t1 [t2 [t3 H_tap]]]].
  exists x, t1, t2, t3.
  destruct H_tap as [? [? [? [? [? [? [[? [HCO ?]] | [y [? [? [HCO ?]]]]]]]]]]].
  - repeat (split; [assumption |]). left.
    repeat (split; [assumption |]). split; [apply Hco_cm; exact HCO |]. assumption.
  - repeat (split; [assumption |]). right. exists y.
    repeat (split; [assumption |]). split; [apply Hco_cm; exact HCO |]. assumption.
Qed.

(** ReadAtomic implies CutIsolation *)
Lemma ReadAtomic_implies_CutIsolation : forall H CM,
  strict_order CM -> ReadAtomic H CM -> CutIsolation H.
Proof.
  intros H CM [Hirrefl Htrans] HRA.
  unfold CutIsolation.
  intros x v v' t t1 t2 r1 r2 w1 w2 Hrt Hwt1 Hn1 Hwt2 Hn2
         Hr1 _ Hr2 _ Hw1 Hw2 Hn12 _ Hwr1 Hwr2.
  (* Extract T-membership without losing WTx/RTx *)
  pose proof (proj1 Hrt) as Ht.
  pose proof (proj1 Hwt1) as Ht1.
  pose proof (proj1 Hwt2) as Ht2.
  destruct Hw1 as [Hw1o [_ Ek1]], Hw2 as [Hw2o [_ Ek2]],
           Hr1 as [Hr1o _], Hr2 as [Hr2o _].
  (* Establish WR relations via wr_implies_WR *)
  assert (HWR1: WR H x t1 t).
  { rewrite <- Ek1. exact (wr_implies_WR H t1 t w1 r1 Ht1 Ht Hn1 Hw1o Hr1o Hwr1). }
  assert (HWR2: WR H x t2 t).
  { rewrite <- Ek2. exact (wr_implies_WR H t2 t w2 r2 Ht2 Ht Hn2 Hw2o Hr2o Hwr2). }
  (* Apply ReadAtomic both ways to derive a CM cycle, contradicting strict order *)
  exfalso. apply (Hirrefl t1). eapply Htrans.
  - apply (HRA x t2 t1 t Hwt2 Hwt1 (fun e => Hn12 (eq_sym e)) Hrt
               (fun e => Hn2 (eq_sym e)) (fun e => Hn1 (eq_sym e)) HWR2).
    right. exists x. exact HWR1.
  - apply (HRA x t1 t2 t Hwt1 Hwt2 Hn12 Hrt
               (fun e => Hn1 (eq_sym e)) (fun e => Hn2 (eq_sym e)) HWR1).
    right. exists x. exact HWR2.
Qed.

(** ReadAtomic implies MonoAtomicView (ReadAtomic is stronger than MonoAtomicView) *)
Lemma ReadAtomic_implies_MonoAtomicView : forall H CM,
  commit_order H CM -> ReadAtomic H CM -> MonoAtomicView H CM.
Proof.
  intros H CM HCM Hra.
  unfold MonoAtomicView.
  intros x y t1 t2 t3 Hxy Hwt1 Hwt2 Hneq12 Hrt3y Hneq31 Hneq32 Hexists.
  destruct Hexists as [wx [wy [rx [ry [Hwx [Hwy [Hrx [Hry [Hpo_ry_rx [Hwry Hwrx]]]]]]]]]].
  (* Extract T-membership without losing WTx/RTx *)
  pose proof (proj1 Hwt1) as Ht1.
  pose proof (proj1 Hwt2) as Ht2.
  pose proof (proj1 Hrt3y) as Ht3.
  (* Build RTx for t3 reading x before destructing Rx *)
  assert (Hrt3x: RTx (T H) x t3) by (split; [exact Ht3 | exists rx; exact Hrx]).
  destruct Hwx as [Hwx_ops [_ Ek_wx]], Hwy as [Hwy_ops [_ Ek_wy]],
           Hrx as [Hrx_ops _], Hry as [Hry_ops _].
  (* Establish WR relations via wr_implies_WR *)
  assert (HWR1: WR H x t1 t3).
  { rewrite <- Ek_wx. exact (wr_implies_WR H t1 t3 wx rx Ht1 Ht3
      (fun e => Hneq31 (eq_sym e)) Hwx_ops Hrx_ops Hwrx). }
  assert (HWR2: WR H y t2 t3).
  { rewrite <- Ek_wy. exact (wr_implies_WR H t2 t3 wy ry Ht2 Ht3
      (fun e => Hneq32 (eq_sym e)) Hwy_ops Hry_ops Hwry). }
  (* Apply ReadAtomic *)
  apply (Hra x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3x Hneq31 Hneq32 HWR1).
  right. exists y. exact HWR2.
Qed.

(** ReadAtomic <-> ~TAP_l *)
Lemma ReadAtomic_iff_no_TAP_l : forall H CM,
  commit_order H CM -> (ReadAtomic H CM <-> ~TAP_l H CM).
Proof.
  intros H CM HCM. split.
  - (* Soundness: ReadAtomic -> ~TAP_l *)
    intros HRa.
    unfold ReadAtomic in HRa.
    unfold TAP_l. intros [x [t1 [t2 [t3 [Hwxt1 [Hwxt2 [Hneq12 [Hrxt3 [Hneq31 [Hneq32 [Hwr | Hso]]]]]]]]]]].
    + destruct Hwr as [Hwr13 [Hcm12 Hso23]].
      assert (Hcm21: CM t2 t1).
      { apply (HRa x t1 t2 t3 Hwxt1 Hwxt2 Hneq12 Hrxt3 Hneq31 Hneq32 Hwr13).
        unfold SO_union_WR. left. tauto. }
      destruct HCM as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
      apply Hirrefl in Hcycle. assumption.
    + destruct Hso as [y [Hryt3 [Hwr13 [Hcm12 Hwr23]]]].
      assert (Hcm21: CM t2 t1).
      { apply (HRa x t1 t2 t3 Hwxt1 Hwxt2 Hneq12 Hrxt3 Hneq31 Hneq32 Hwr13).
        unfold SO_union_WR. right. exists y. tauto. }
      destruct HCM as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
      apply Hirrefl in Hcycle. assumption.
  - (* Completeness: ~TAP_l -> ReadAtomic *)
    intros Hno_l.
    unfold ReadAtomic.
    intros x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hso_wr.
    (* Use totality of CM: either CM t1 t2 or CM t2 t1 *)
    destruct HCM as [_ [Htot _]].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21]; auto.
    (* Case: CM t1 t2 - derive contradiction via TAP_l *)
    exfalso. apply Hno_l.
    unfold TAP_l.
    exists x, t1, t2, t3.
    repeat (split; [assumption |]).
    unfold SO_union_WR in Hso_wr.
    destruct Hso_wr as [Hso23 | [y Hwr23]].
    + (* SO t2 t3 case *)
      left. split; [exact Hwr13 |]. split; [exact Hcm12 |]. exact Hso23.
    + (* WR y t2 t3 case *)
      right.
      pose proof (proj1 (wr_iff_WR H y t2 t3) Hwr23)
        as [_ [Ht3 [_ [w [r [_ [Hrx _]]]]]]].
      exists y.
      split.
      { unfold RTx. split; [exact Ht3 | exists r; exact Hrx]. }
      split; [exact Hwr13 |].
      split; [exact Hcm12 |].
      exact Hwr23.
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
    + (* TAP_h: reduce to TAP_i, then use MonoAtomicView_iff_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      intros Htap_h.
      apply (TAP_h_implies_TAP_i H CM (conj Hstrict HCM_rest)) in Htap_h.
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM (conj Hstrict HCM_rest)) HMono Htap_h).
    + (* TAP_i: use MonoAtomicView_iff_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM (conj Hstrict HCM_rest)) HMono).
    + (* TAP_j: use CI_soundness_completeness *)
      apply CI_soundness_completeness. exact HCI.
    + (* TAP_k: reduce to TAP_l via TAP_k_implies_TAP_l *)
      intros Htap_k.
      apply (TAP_k_implies_TAP_l H CM (conj Hstrict HCM_rest)) in Htap_k.
      exact (proj1 (ReadAtomic_iff_no_TAP_l H CM (conj Hstrict HCM_rest)) HReadAtomic Htap_k).
    + (* TAP_l: use ReadAtomic_iff_no_TAP_l directly *)
      exact (proj1 (ReadAtomic_iff_no_TAP_l H CM (conj Hstrict HCM_rest)) HReadAtomic).
  - (* Completeness: no TAPs a-l -> RA *)
    intros [CM [HCM Hno_taps]].
    unfold ReadAtomicity.
    unfold no_TAP_a_to_l in Hno_taps.
    destruct Hno_taps as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    unfold no_TAP_a_to_i in Hno_ai.
    destruct Hno_ai as [Hno_ag [Hno_h Hno_i]].
    assert (HRC: RC1 H /\ RC2 H /\ RC3 H).
    { apply RC123_iff_no_TAP_a_to_g. exact Hno_ag. }
    destruct HRC as [HRC1 [HRC2 HRC3]].
    repeat split; auto.
    exists CM. split. assumption.
    (* ~TAP_l -> ReadAtomic via ReadAtomic_iff_no_TAP_l *)
    apply (proj2 (ReadAtomic_iff_no_TAP_l H CM HCM)). exact Hno_l.
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
  repeat (split; [assumption |]).
  split; [apply Hco_cm; exact Hco12 |].
  exact Hco23.
Qed.

(** Causal <-> ~TAP_n *)
Lemma Causal_iff_no_TAP_n : forall H CM,
  commit_order H CM -> (Causal H CM <-> ~TAP_n H CM).
Proof.
  intros H CM HCM. split.
  - (* Soundness: Causal -> ~TAP_n *)
    intros HCausal.
    unfold TAP_n. intros [x [t1 [t2 [t3 [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hneq31 [Hneq32 [Hwr13 [Hcm12 Hco23]]]]]]]]]]]].
    assert (Hcm21: CM t2 t1).
    { apply (HCausal x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hco23). }
    destruct HCM as [Hstrict _].
    unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
    assert (Hcycle: CM t1 t1). { eapply Htrans; [exact Hcm12 | exact Hcm21]. }
    apply Hirrefl in Hcycle. assumption.
  - (* Completeness: ~TAP_n -> Causal *)
    intros Hno_n.
    unfold Causal.
    intros x t1 t2 t3 Hwt1 Hwt2 Hneq12 Hrt3 Hneq31 Hneq32 Hwr13 Hco23.
    destruct HCM as [_ [Htot _]].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21]; auto.
    exfalso. apply Hno_n.
    unfold TAP_n.
    exists x, t1, t2, t3.
    repeat (split; [assumption |]).
    exact Hco23.
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
    + (* TAP_h: reduce to TAP_i, then use MonoAtomicView_iff_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      intros Htap_h.
      apply (TAP_h_implies_TAP_i H CM (conj Hstrict HCM_rest)) in Htap_h.
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM (conj Hstrict HCM_rest)) HMono Htap_h).
    + (* TAP_i: use MonoAtomicView_iff_no_TAP_i *)
      assert (HMono: MonoAtomicView H CM).
      { apply (ReadAtomic_implies_MonoAtomicView H CM (conj Hstrict HCM_rest) HReadAtomic). }
      exact (proj1 (MonoAtomicView_iff_no_TAP_i H CM (conj Hstrict HCM_rest)) HMono).
    + (* TAP_j: use CI_soundness_completeness *)
      apply CI_soundness_completeness.
      apply (ReadAtomic_implies_CutIsolation H CM Hstrict HReadAtomic).
    + (* TAP_k: use ReadAtomic_iff_no_TAP_l via TAP_k_implies_TAP_l *)
      intros Htap_k.
      apply (TAP_k_implies_TAP_l H CM (conj Hstrict HCM_rest)) in Htap_k.
      exact (proj1 (ReadAtomic_iff_no_TAP_l H CM (conj Hstrict HCM_rest)) HReadAtomic Htap_k).
    + (* TAP_l: use ReadAtomic_iff_no_TAP_l directly *)
      exact (proj1 (ReadAtomic_iff_no_TAP_l H CM (conj Hstrict HCM_rest)) HReadAtomic).
    + (* TAP_m: reduce to TAP_n via TAP_m_implies_TAP_n *)
      intros Htap_m.
      apply (TAP_m_implies_TAP_n H CM (conj Hstrict HCM_rest)) in Htap_m.
      exact (proj1 (Causal_iff_no_TAP_n H CM (conj Hstrict HCM_rest)) HCausal Htap_m).
    + (* TAP_n: use Causal_iff_no_TAP_n directly *)
      exact (proj1 (Causal_iff_no_TAP_n H CM (conj Hstrict HCM_rest)) HCausal).
  - (* Completeness: no all TAPs -> TCC *)
    intros [CM [HCM Hno_taps]].
    unfold TransactionalCausalConsistency.
    unfold no_all_TAPs in Hno_taps.
    destruct Hno_taps as [Hno_al [Hno_m Hno_n]].
    unfold no_TAP_a_to_l in Hno_al.
    destruct Hno_al as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    unfold no_TAP_a_to_i in Hno_ai.
    destruct Hno_ai as [Hno_ag [Hno_h Hno_i]].
    assert (HRC: RC1 H /\ RC2 H /\ RC3 H).
    { apply RC123_iff_no_TAP_a_to_g. exact Hno_ag. }
    destruct HRC as [HRC1 [HRC2 HRC3]].
    repeat split; auto.
    exists CM. split. assumption.
    (* ~TAP_n -> Causal via Causal_iff_no_TAP_n *)
    apply (proj2 (Causal_iff_no_TAP_n H CM HCM)). exact Hno_n.
Qed.
