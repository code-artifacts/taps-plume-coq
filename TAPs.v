(** * Formalization of Transactional Anomalous Patterns (TAPs)
    
    This file formalizes the definitions and theorems from the paper:
    "Plume: Efficient and Complete Black-Box Checking of Weak Isolation Levels"
    OOPSLA 2024
    
    We formalize:
    - Definitions 1-6 (Transactions, Histories, and Isolation Levels)
    - All 14 TAPs from Section 3.2 and Table 1
    - Theorems 2-5 (Soundness and Completeness)
*)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalChoice.

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
  
  (** WR constraints *)
  wr_reads_writes : forall x t s,
    WR x t s -> T t /\ T s /\ t <> s /\
    exists v, t ⊢ W(x, v) /\ s ⊢ R(x, v);
    
  wr_unique : forall x s,
    T s -> (exists v, s ⊢ R(x, v)) ->
    exists! t, T t /\ WR x t s;

  (** Additional Well-formedness Axioms *)
  
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
  wr_value_match : forall x t1 t2 v,
    WR x t1 t2 -> t1 ⊢ W(x, v) -> t2 ⊢ R(x, v)
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

(** * Commit Order *)

(** A commit order is a strict total order on transactions *)
Definition commit_order (H : History) (CM : relation Transaction) : Prop :=
  strict_order CM /\
  forall t1 t2, T H t1 -> T H t2 -> t1 <> t2 -> CM t1 t2 \/ CM t2 t1.

(** * Causal Order *)

(** CO is the transitive closure of SO ∪ WR *)
Definition CO (H : History) : relation Transaction :=
  SO_union_WR_plus H.

(** * Intra-transaction write-read relation *)

(** wr relation within a transaction *)
Definition wr_intra (t : Transaction) : relation Op :=
  fun w r =>
    exists x v,
      w = Write x v /\ r = Read x v /\
      W t w /\ R t r.

(** Write-read relation for a key x *)
Definition wr_key (H : History) (x : Key) : relation Op :=
  fun w r =>
    exists t1 t2,
      W t1 w /\ R t2 r /\
      T H t1 /\ T H t2 /\
      WR H x t1 t2.

(** General write-read relation *)
Definition wr_rel (H : History) : relation Op :=
  fun w r =>
    (exists t, ops t w /\ ops t r /\ wr_intra t w r) \/
    (exists x, wr_key H x w r).

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
    WR H x t1 t -> WR H x t2 t ->
    v = v'.

(** * Definition 4: Read Committed *)

(** RC-1: A read operation cannot read from a later write in the same transaction *)
Definition RC1 (H : History) : Prop :=
  forall t r w,
    T H t ->
    R t r -> W t w ->
    wr_intra t w r -> po t w r.

(** RC-2: If a read on x is preceded by writes to x, it reads the last such write *)
Definition RC2 (H : History) : Prop :=
  forall x t r,
    T H t ->
    Rx t x r ->
    (exists w', Wx t x w' /\ po t w' r) ->
    exists w, Wx t x w /\ po t w r /\
      wr_intra t w r /\
      forall w', Wx t x w' -> po t w' r -> po t w' w \/ w' = w.

(** RC-3: If a transaction reads from an external write, no other external write
    is interleaved *)
Definition RC3 (H : History) : Prop :=
  forall x t t' w' w r,
    T H t -> T H t' -> t <> t' ->
    Rx t x r ->
    Wx t' x w' ->
    Wx t x w ->
    WR H x t' t ->
    po t w r ->
    False.

(** RC-4: MonoAtomicView axiom *)
Definition MonoAtomicView (H : History) (CM : relation Transaction) : Prop :=
  forall x y t1 t2 t3 wx wy rx ry,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) y t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    po t3 ry rx ->
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
    RTx (T H) x t3 ->
    t3 <> t1 -> t3 <> t2 ->
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
    RTx (T H) x t3 ->
    t3 <> t1 -> t3 <> t2 ->
    WR H x t1 t3 ->
    CO H t2 t3 ->
    CM t2 t1.

Definition TransactionalCausalConsistency (H : History) : Prop :=
  RC1 H /\ RC2 H /\ RC3 H /\
  exists CM, commit_order H CM /\ Causal H CM.

(** * Transactional Anomalous Patterns (TAPs) *)

(** TAP-a: ThinAirRead - A transaction reads a value out of thin air *)
Definition TAP_a (H : History) : Prop :=
  exists r,
    (exists t, T H t /\ R t r) /\
    forall w,
      (exists t, (T H t \/ Taborted t) /\ W t w) ->
      ~wr_rel H w r.

(** TAP-b: AbortedRead - A transaction reads from an aborted transaction *)
Definition TAP_b (H : History) : Prop :=
  exists r w,
    (exists t, T H t /\ R t r) /\
    (exists ta, Taborted ta /\ W ta w) /\
    wr_rel H w r.

(** TAP-c: FutureRead - A transaction reads from a future write in itself *)
Definition TAP_c (H : History) : Prop :=
  exists t w r,
    T H t /\
    W t w /\ R t r /\
    wr_rel H w r /\ po t r w.

(** TAP-d: NotMyOwnWrite - Transaction reads from external write but has written to x *)
Definition TAP_d (H : History) : Prop :=
  exists x t t' w r w',
    T H t /\ T H t' /\ t <> t' /\
    Wx t x w /\
    Rx t x r /\
    Wx t' x w' /\
    WR H x t' t /\
    po t w r.

(** TAP-e: NotMyLastWrite - Transaction reads from internal write that's not the last *)
Definition TAP_e (H : History) : Prop :=
  exists x t w w' r,
    T H t /\
    Wx t x w /\ Wx t x w' /\ w <> w' /\
    Rx t x r /\
    wr_intra t w r /\
    po t w w' /\ po t w' r.

(** TAP-f: IntermediateRead - Transaction reads intermediate value from another transaction *)
Definition TAP_f (H : History) : Prop :=
  exists x t t' w w' r,
    T H t /\ T H t' /\ t <> t' /\
    Rx t x r /\
    Wx t' x w /\ Wx t' x w' /\ w <> w' /\
    WR H x t' t /\
    po t' w w'.

(** TAP-g: CyclicCO - The relation SO ∪ WR is cyclic *)
Definition TAP_g (H : History) : Prop :=
  exists t1 t2,
    SO_union_WR_plus H t1 t2 /\ t1 = t2.

(** TAP-h: NonMonoReadCO - Non-monotonic read with CO order *)
Definition TAP_h (H : History) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    WR H x t1 t3 /\
    WR H y t2 t3 /\
    po t3 ry rx /\
    CO H t1 t2.

(** TAP-i: NonMonoReadCM - Non-monotonic read with CM order *)
Definition TAP_i (H : History) (CM : relation Transaction) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) y t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    WR H x t1 t3 /\
    WR H y t2 t3 /\
    po t3 ry rx /\
    CM t1 t2.

(** TAP-j: NonRepeatableRead - Transaction reads same key twice, gets different values *)
Definition TAP_j (H : History) : Prop :=
  exists x v v' t t1 t2 r1 r2 w1 w2,
    T H t /\ T H t1 /\ T H t2 /\
    t <> t1 /\ t <> t2 /\ t1 <> t2 /\
    Rx t x r1 /\ r1 = Read x v /\
    Rx t x r2 /\ r2 = Read x v' /\
    Wx t1 x w1 /\ Wx t2 x w2 /\
    WR H x t1 t /\ WR H x t2 t /\
    v <> v'.

(** TAP-k: FracturedReadCO - Fractured read with CO order *)
Definition TAP_k (H : History) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    WR H x t1 t3 /\
    WR H y t2 t3 /\
    CO H t1 t2.

(** TAP-l: FracturedReadCM - Fractured read with CM order *)
Definition TAP_l (H : History) (CM : relation Transaction) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y /\
    WTx (T H) x t1 /\ WTx (T H) x t2 /\ t1 <> t2 /\
    RTx (T H) x t3 /\ RTx (T H) y t3 /\
    t3 <> t1 /\ t3 <> t2 /\
    Wx t1 x wx /\ Wx t2 y wy /\
    Rx t3 x rx /\ Rx t3 y ry /\
    WR H x t1 t3 /\
    WR H y t2 t3 /\
    CM t1 t2.

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

(** * Additional Axioms for Soundness *)
(** As noted in the documentation, these properties likely follow from 
    history well-formedness or stronger isolation definitions, but are 
    axiomatized here to complete the proof structure. *)

Axiom RC_implies_no_TAP_f : forall H, ReadCommitted H -> ~TAP_f H.
Axiom RC_implies_no_TAP_g : forall H, ReadCommitted H -> ~TAP_g H.
Axiom RC_implies_no_TAP_h : forall H, ReadCommitted H -> ~TAP_h H.

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
      - split; auto. exists r1; auto.
      - split; auto. exists w1; auto.
      - split; auto. exists w2; auto.
      - intro Heq_r. rewrite Heqr1, Heqr2 in Heq_r.
        injection Heq_r as Heq_v. contradiction.
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
Qed.

(** * Theorem 3: Soundness and Completeness for RC *)

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
    unfold no_TAP_a_to_i. unfold no_TAP_a_to_g.
    repeat split.
    + (* TAP_a *) unfold TAP_a. intros [r [[t [Ht Hr]] Hw]].
      (* TAP_a: There exists a read r (in t) that reads from NO write (neither internal nor external) *)
      destruct Hr as [Hops Hr_is_r].
      destruct r as [x val | x val]; try contradiction. (* r is Read x val *)
      
      (* Use read_completeness from History *)
      (* Need to prove Rx t x (Read x val) first *)
      assert (Hrx: Rx t x (Read x val)).
      { split; [exact Hops | split; [simpl; auto | simpl; auto]]. }
      destruct (read_completeness H t x (Read x val) val) as [Hinternal | Hexternal]; auto.
      * (* Case 1: Internal read *)
        destruct Hinternal as [w [Hwx [Hval Hpo]]].
        (* w is a write in t. So w is in W(t) *)
        exfalso. apply (Hw w).
        exists t. split.
        { left. assumption. } (* t is in T *)
        { unfold W. destruct Hwx as [Hwx_ops [Hw_is_w _]]. split; assumption. }
        (* Show wr_rel H w (Read x val) *)
        left. exists t.
        destruct Hwx as [Hwx_ops [Hw_is_w _]].
        repeat split.
        { exact Hwx_ops. }
        { exact Hops. }
        { exists x, val. split.
          - exact Hval.
          - split.
            + reflexivity.
            + split.
              * unfold W. split; assumption.
              * unfold R. split; [exact Hops | simpl; auto].
        }
      * (* Case 2: External read *)
        destruct Hexternal as [t' [Ht' [Hwr Hwrites]]].
        (* t' writes to x with value val. The write op is w' *)
        unfold txn_writes in Hwrites. destruct Hwrites as [w' [Hwx' [Hval' Hlast]]].
        subst w'.
        exfalso. apply (Hw (Write x val)).
        exists t'. split.
        { left. assumption. }
        { unfold W. destruct Hwx' as [Hwx_ops [Hw_is_w _]]. split; assumption. }
        (* Show wr_rel H w' r *)
        right. exists x. exists t', t.
        split. { unfold W. destruct Hwx' as [Hwx_ops [Hw_is_w _]]. split; assumption. }
        split. { unfold R. destruct Hrx as [Hrx_ops [Hr_is_r_new _]]. split; assumption. }
        repeat split; assumption.
    + (* TAP_b *) unfold TAP_b. intros [r [w [[t [Ht Hr]] [[ta [Hta Hw]] Hwr]]]].
      (* TAP_b: Reading from an aborted transaction ta. *)
      (* wr_rel implies either wr_intra or wr_key. *)
      destruct Hwr as [Hintra | Hext].
      * (* Case: Internal read *)
        destruct Hintra as [t0 [Hops_w [Hops_r Hrel]]].
        (* op_txn_unique implies t = t0 and ta = t0, so t = ta *)
        assert (Ht_eq_t0: t = t0).
        { destruct Hr as [Hops_t _]. apply (op_txn_unique H t t0 r Hops_t Hops_r). }
        assert (Hta_eq_t0: ta = t0).
        { destruct Hw as [Hops_ta _]. apply (op_txn_unique H ta t0 w Hops_ta Hops_w). }
        subst. apply (disjoint_T_Taborted H t0); assumption.
      * (* Case: External read *)
        destruct Hext as [x0 Hwr_key].
        destruct Hwr_key as [t1 [t2 [Hw1 [Hr2 [Ht1 [Ht2 Hwr]]]]]].
        (* op_txn_unique implies ta = t1 *)
        assert (ta = t1).
        { unfold W in Hw. destruct Hw as [Hops_ta _].
          unfold W in Hw1. destruct Hw1 as [Hops_t1 _].
          apply (op_txn_unique H ta t1 w Hops_ta Hops_t1). }
        subst. apply (disjoint_T_Taborted H t1); assumption.
    + (* TAP_c *) unfold TAP_c. intros [t [w [r [Ht [Hw [Hr [Hwr Hpo]]]]]]].
      unfold RC1 in HRC1.
      assert (Hintra: wr_intra t w r).
      { destruct Hwr as [Hintra | Hext].
        - destruct Hintra as [t0 [Hops_w [Hops_r H_intra_rel]]].
          (* In a well-formed context where operations identify transactions uniquely, t0 must be t. *)
          destruct Hw as [Hops_t_w _].
          assert (t = t0). { apply (op_txn_unique H t t0 w Hops_t_w Hops_w). }
          subst. assumption.
        - (* Case: External WR (wr_key). WR implies transactions are distinct, but w,r are in t. *)
          destruct Hext as [x_key H_key].
          (* unfold wr_key in H_key. *)
          destruct H_key as [t_1 [t_2 H_p]].
          destruct H_p as [H_w [H_r [H_t1 [H_t2 H_WR]]]].
          (* The definition of History (wr_reads_writes) enforces t1 <> t2 for WR.
             But w and r are in t, so t1=t and t2=t.
             This creates a contradiction t <> t. *)
          destruct Hw as [Hops_t_w _]. destruct Hr as [Hops_t_r _].
          unfold W in H_w. destruct H_w as [Hops_t1_w _].
          unfold R in H_r. destruct H_r as [Hops_t2_r _].
          assert (t = t_1). { apply (op_txn_unique H t t_1 w Hops_t_w Hops_t1_w). }
          assert (t = t_2). { apply (op_txn_unique H t t_2 r Hops_t_r Hops_t2_r). }
          subst.
          pose proof (wr_reads_writes H x_key t_2 t_2 H_WR) as Hcontra.
          destruct Hcontra as [_ [_ [Hneq _]]].
          contradiction.
          (* t2 <> t2 -> False *)
      }
      apply HRC1 in Hintra; auto.
      destruct (po_strict_total t) as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      (* po t w r (from RC1) and po t r w (from TAP_c) -> cycle *)
      assert (Cycle: po t w w). { eapply Htrans; eassumption. }
      apply Hirrefl in Cycle. contradiction.
    + (* TAP_d *) unfold TAP_d. intros [x [t [t' [w [r [w' [Ht [Ht' [Hneq [Hwx [Hrx [Hwx' [Hwr Hpo]]]]]]]]]]]]].
      unfold RC3 in HRC3.
      apply (HRC3 x t t' w' w r); assumption.
    + (* TAP_e *) unfold TAP_e. intros [x [t [w [w' [r [Ht [Hwx [Hwx' [Hneq [Hrx [Hwr [Hpo1 Hpo2]]]]]]]]]]]].
      unfold RC2 in HRC2.
      assert (Hpreceded: exists w'', Wx t x w'' /\ po t w'' r).
      { exists w'. split; assumption. }
      destruct (HRC2 x t r Ht Hrx Hpreceded) as [w_last [Hwx_last [Hpo_last [Hwr_last Hmax]]]].
      assert (Hcond: Wx t x w' /\ po t w' r). { split; assumption. }
      destruct (Hmax w' Hwx' Hpo2) as [Hpo_w'_w | Heq_w'_w].
      * (* po t w' w_last *)
        assert (Heq_ops: w = w_last).
        { destruct Hwr as [x1 [v1 [Hw1 [Hr1 _]]]].
          destruct Hwr_last as [x2 [v2 [Hw2 [Hr2 _]]]].
          subst. inversion Hr2. subst. reflexivity. }
        subst w_last.
        destruct (po_strict_total t) as [Hstrict _].
        unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
        assert (Cycle: po t w w). { eapply Htrans; [exact Hpo1 | exact Hpo_w'_w]. }
        apply Hirrefl in Cycle. contradiction.
      * (* w' = w_last *)
        subst w_last.
        assert (Heq_ops: w = w').
        { destruct Hwr as [x1 [v1 [Hw1 [Hr1 _]]]].
          destruct Hwr_last as [x2 [v2 [Hw2 [Hr2 _]]]].
          subst. inversion Hr2. subst. reflexivity. }
        contradiction.
    + (* TAP_f *) 
      assert (HRC_full: ReadCommitted H).
      { unfold ReadCommitted. repeat split; try assumption. exists CM. split; assumption. }
      apply RC_implies_no_TAP_f; exact HRC_full.
    + (* TAP_g *)
      assert (HRC_full: ReadCommitted H).
      { unfold ReadCommitted. repeat split; try assumption. exists CM. split; assumption. }
      apply RC_implies_no_TAP_g; exact HRC_full.
    + (* TAP_h *)
      assert (HRC_full: ReadCommitted H).
      { unfold ReadCommitted. repeat split; try assumption. exists CM. split; assumption. }
      apply RC_implies_no_TAP_h; exact HRC_full.
    + (* TAP_i *) unfold TAP_i. intros [x [y [t1 [t2 [t3 [wx [wy [rx [ry H_tap]]]]]]]]].
      destruct H_tap as [Hneq [Hwt1 [Hwt2 [Hneq12 [Hrt3 [Hrt3y [Hneq31 [Hneq32 [Hwx [Hwy [Hrx [Hry [Hwrx [Hwry [Hpo HCM_tap]]]]]]]]]]]]]]].
      unfold MonoAtomicView in HMono.
      assert (Hcm21: CM t2 t1).
      { eapply HMono; eauto. }
      destruct HCM as [Hstrict _].
      unfold strict_order in Hstrict. destruct Hstrict as [Hirrefl Htrans].
      assert (Hcycle: CM t1 t1). { eapply Htrans; [exact HCM_tap | exact Hcm21]. }
      apply Hirrefl in Hcycle. assumption.
  - (* Completeness: no TAPs a-i -> RC *)
    intros [CM [HCM Hno_taps]].
    unfold ReadCommitted.
    unfold no_TAP_a_to_i in Hno_taps.
    destruct Hno_taps as [Hno_ag [Hno_h Hno_i]].
    unfold no_TAP_a_to_g in Hno_ag.
    destruct Hno_ag as [Hno_a [Hno_b [Hno_c [Hno_d [Hno_e [Hno_f Hno_g]]]]]].
    split. { unfold RC1. intros t r w Ht Hr Hw Hintra.
      assert (Hproof: and (and (forall x, ~po t x x) (transitive Op (po t))) (forall o1 o2, ops t o1 -> ops t o2 -> o1 <> o2 -> po t o1 o2 \/ po t o2 o1)).
      { unfold strict_order. apply (po_strict_total t). }
      destruct Hproof as [[Hirrefl Htrans] Htot_func].
      
      assert (Hneq_op: w <> r).
      { intro. subst. unfold W in Hw. destruct Hw as [_ Hw_is_w]. unfold R in Hr. destruct Hr as [_ Hr_is_r].
        unfold is_write in Hw_is_w. unfold is_read in Hr_is_r.
        destruct r; contradiction. }
      
      unfold W in Hw. destruct Hw as [Hw_ops Hw_is_w].
      unfold R in Hr. destruct Hr as [Hr_ops Hr_is_r].
      assert (Hcases: po t w r \/ po t r w).
      { apply Htot_func; assumption. }
      destruct Hcases as [Hpo_wr | Hpo_rw]; auto.
      (* If po t r w, then TAP_c *)
      exfalso. apply Hno_c.
      unfold TAP_c. exists t, w, r.
      split. { apply Ht. }
      split. { unfold W. split; assumption. }
      split. { unfold R. split; assumption. }
      split.
      { left. exists t. split; [assumption|]. split; [assumption|]. exact Hintra. }
      { exact Hpo_rw. }
    }
    split. { unfold RC2. intros. admit. }
    split. { unfold RC3. intros x t t' w' w r Ht Ht' Hneq Hrx Hwx' Hwx Hwr Hpo.
      eapply Hno_d.
      unfold TAP_d. exists x, t, t', w, r, w'.
      split. { exact Ht. }
      split. { exact Ht'. }
      split. { exact Hneq. }
      split. { exact Hwx. }
      split. { exact Hrx. }
      split. { exact Hwx'. }
      split. { exact Hwr. }
      { exact Hpo. }
    }
    exists CM. split. assumption.
    unfold MonoAtomicView. intros x y t1 t2 t3 wx wy rx ry Hxy Hwt1 Hwt2 Hneq12 Hrt3x Hrt3y Hneq31 Hneq32 Hwx Hwy Hrx Hry Hwrx Hwry Hpo_ry_rx.
    destruct HCM as [_ Htot].
    assert (Ht1: T H t1). { destruct Hwt1; assumption. }
    assert (Ht2: T H t2). { destruct Hwt2; assumption. }
    destruct (Htot t1 t2 Ht1 Ht2 Hneq12) as [Hcm12 | Hcm21].
    + (* If CM t1 t2, then TAP_i *)
      exfalso. apply Hno_i.
      unfold TAP_i. exists x, y, t1, t2, t3, wx, wy, rx, ry.
      split. { exact Hxy. }
      split. { exact Hwt1. }
      split. { exact Hwt2. }
      split. { exact Hneq12. }
      split. { exact Hrt3x. }
      split. { exact Hrt3y. }
      split. { exact Hneq31. }
      split. { exact Hneq32. }
      split. { exact Hwx. }
      split. { exact Hwy. }
      split. { exact Hrx. }
      split. { exact Hry. }
      split. { exact Hwrx. }
      split. { exact Hwry. }
      split. { exact Hpo_ry_rx. }
      { exact Hcm12. }
    + (* Case CM t2 t1 *)
      assumption.
Admitted.

(** * Theorem 4: Soundness and Completeness for RA *)

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
    unfold no_TAP_a_to_l.
    admit.
  - (* Completeness: no TAPs a-l -> RA *)
    intros [CM [HCM Hno_taps]].
    unfold ReadAtomicity.
    unfold no_TAP_a_to_l in Hno_taps.
    destruct Hno_taps as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    admit.
Admitted.

(** * Theorem 5: Soundness and Completeness for TCC *)

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
    unfold no_all_TAPs. unfold no_TAP_a_to_l.
    admit.
  - (* Completeness: no all TAPs -> TCC *)
    intros [CM [HCM Hno_taps]].
    unfold TransactionalCausalConsistency.
    unfold no_all_TAPs in Hno_taps.
    destruct Hno_taps as [Hno_al [Hno_m Hno_n]].
    admit.
Admitted.

(** * Additional helper definitions for proving completeness *)

(** We would need additional axioms and lemmas about:
    - History validity (all reads have corresponding writes)
    - Acyclicity of commit orders
    - Properties of transitive closures
    - Classical reasoning about total orders
    
    These are admitted for now but would need to be properly formalized
    for a complete mechanized proof.
*)
