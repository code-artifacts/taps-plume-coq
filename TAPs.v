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
    exists! t, T t /\ WR x t s
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
    po t w r -> wr_intra t w r.

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
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    po t3 ry rx ->
    CM t1 t2.

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
    T H t -> T H t' -> t <> t' ->
    Wx t x w ->
    Rx t x r ->
    Wx t' x w' ->
    WR H x t' t ->
    po t w r.

(** TAP-e: NotMyLastWrite - Transaction reads from internal write that's not the last *)
Definition TAP_e (H : History) : Prop :=
  exists x t w w' r,
    T H t ->
    Wx t x w -> Wx t x w' -> w <> w' ->
    Rx t x r ->
    wr_intra t w r ->
    po t w w' /\ po t w' r.

(** TAP-f: IntermediateRead - Transaction reads intermediate value from another transaction *)
Definition TAP_f (H : History) : Prop :=
  exists x t t' w w' r,
    T H t -> T H t' -> t <> t' ->
    Rx t x r ->
    Wx t' x w -> Wx t' x w' -> w <> w' ->
    WR H x t' t ->
    po t' w w'.

(** TAP-g: CyclicCO - The relation SO ∪ WR is cyclic *)
Definition TAP_g (H : History) : Prop :=
  exists t1 t2,
    SO_union_WR_plus H t1 t2 /\ t1 = t2.

(** TAP-h: NonMonoReadCO - Non-monotonic read with CO order *)
Definition TAP_h (H : History) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    po t3 ry rx ->
    CO H t1 t2.

(** TAP-i: NonMonoReadCM - Non-monotonic read with CM order *)
Definition TAP_i (H : History) (CM : relation Transaction) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    po t3 ry rx ->
    CM t1 t2.

(** TAP-j: NonRepeatableRead - Transaction reads same key twice, gets different values *)
Definition TAP_j (H : History) : Prop :=
  exists x v v' t t1 t2 r1 r2 w1 w2,
    T H t -> T H t1 -> T H t2 ->
    t <> t1 -> t <> t2 -> t1 <> t2 ->
    Rx t x r1 -> r1 = Read x v ->
    Rx t x r2 -> r2 = Read x v' ->
    Wx t1 x w1 -> Wx t2 x w2 ->
    WR H x t1 t -> WR H x t2 t ->
    v <> v'.

(** TAP-k: FracturedReadCO - Fractured read with CO order *)
Definition TAP_k (H : History) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    CO H t1 t2.

(** TAP-l: FracturedReadCM - Fractured read with CM order *)
Definition TAP_l (H : History) (CM : relation Transaction) : Prop :=
  exists x y t1 t2 t3 wx wy rx ry,
    x <> y ->
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 -> RTx (T H) y t3 ->
    t3 <> t1 -> t3 <> t2 ->
    Wx t1 x wx -> Wx t2 y wy ->
    Rx t3 x rx -> Rx t3 y ry ->
    WR H x t1 t3 ->
    WR H y t2 t3 ->
    CM t1 t2.

(** TAP-m: COConflictCM - CO and CM order conflict *)
Definition TAP_m (H : History) (CM : relation Transaction) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 ->
    t3 <> t1 -> t3 <> t2 ->
    WR H x t1 t3 ->
    CO H t1 t2 -> CO H t2 t3.

(** TAP-n: ConflictCM - CM and CO order conflict *)
Definition TAP_n (H : History) (CM : relation Transaction) : Prop :=
  exists x t1 t2 t3,
    WTx (T H) x t1 -> WTx (T H) x t2 -> t1 <> t2 ->
    RTx (T H) x t3 ->
    t3 <> t1 -> t3 <> t2 ->
    WR H x t1 t3 ->
    CM t1 t2 -> CO H t2 t3.

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
    (* The rest uses classical reasoning and would need to extract all the conjuncts *)
    admit.
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
    repeat split; auto.
Admitted.

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
    repeat split; unfold not; intros HTAP; admit.
  - (* Completeness: no TAPs a-i -> RC *)
    intros [CM [HCM Hno_taps]].
    unfold ReadCommitted.
    unfold no_TAP_a_to_i in Hno_taps.
    destruct Hno_taps as [Hno_ag [Hno_h Hno_i]].
    unfold no_TAP_a_to_g in Hno_ag.
    destruct Hno_ag as [Hno_a [Hno_b [Hno_c [Hno_d [Hno_e [Hno_f Hno_g]]]]]].
    split. { unfold RC1. intros. admit. }
    split. { unfold RC2. intros. admit. }
    split. { unfold RC3. intros. admit. }
    exists CM. split. assumption.
    unfold MonoAtomicView. intros. admit.
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
    (* RA is stronger than RC, so we inherit TAP_a to TAP_i *)
    admit.
  - (* Completeness: no TAPs a-l -> RA *)
    intros [CM [HCM Hno_taps]].
    unfold ReadAtomicity.
    unfold no_TAP_a_to_l in Hno_taps.
    destruct Hno_taps as [Hno_ai [Hno_j [Hno_k Hno_l]]].
    (* First establish RC from no TAPs a-i *)
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
    (* TCC is stronger than RA, so we inherit TAP_a to TAP_l *)
    admit.
  - (* Completeness: no all TAPs -> TCC *)
    intros [CM [HCM Hno_taps]].
    unfold TransactionalCausalConsistency.
    unfold no_all_TAPs in Hno_taps.
    destruct Hno_taps as [Hno_al [Hno_m Hno_n]].
    (* First establish RA from no TAPs a-l *)
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
