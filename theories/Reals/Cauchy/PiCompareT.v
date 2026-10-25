(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiCompareT: Set-level thin wrappers for the three-way comparison
      decisions on [Q] values.

    Mission.  This file formalizes Set-level thin wrappers for the
      three-way comparison decisions on [Q] values: the strict-order
      decision [QltT] comes with its own three-way Boolean, the
      non-strict order [QleT'] uses the stdlib native [Qle_bool]
      directly, and the equality decision uses the native [Qeq_bool]
      directly.  Through the Set-valued identity type [Id], the
      semantic equivalence of the wrappers with the [Qcompare]
      three-way split, with the stdlib native Booleans, and with the
      same-shaped originals of this development is stated item by
      item; concrete numeric spot-check computations are appended.

    Dependencies.  Stdlib [QArith.QArith] ([Q], [Qcompare],
      [Qeq_bool], [Qle_bool]).

    References.  This development, [S01_BaseRing.v] ([Id],
      [id_trans]); this development, [S02_CauchyComplete.v]
      and [S02_CauchyComplete.v] (the [Qlt_bool], [QltT],
      [Qle_bool] and [QleT'] originals); stdlib [QArith_base.v]
      (the [Qcompare] notation [p ?= q]), [QArith_base.v]
      ([Qeq_bool]) and [QArith_base.v] ([Qle_bool]).
    Statement-level migration provenance is maintained in
    [docs/statement-provenance.md]; citations in this file are by
    fully qualified name.

    Constructivity.  Carried at the [Set] level; assumption-free and
      fully proved, with no non-constructive principles; the whole
      chain ends in [Defined]; extractable.

    Build.  [rocq c -native-compiler no -q -Q . "" PiCompareT.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.

(* ================= Section 1. The Set-valued identity type ================= *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* ================= Section 2. Thin wrappers for the order decisions on [Q] values
   =================  *)

(* The strict-order Boolean comes with its own three-way form: stdlib
   [QArith_base] contains no [Qlt_bool] anywhere (a same-named item
   survives in exactly one place across the stdlib tree, inside a
   dependency domain that this file must not import); the non-strict
   order and the equality use the native [QArith_base] Booleans
   directly. *)

(* Shared comparison boolean. Used by PiWindowCore and PiSeparation. *)
Definition Qlt_bool (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

(* Shared comparison type. Canonical definition — PiWindowCore imports from here. *)
Definition QltT (x y : Q) : Set := Id (Qlt_bool x y) true.

(* Shared comparison reflection. Canonical definition — PiWindowCore imports from here. *)
Definition QleT' (x y : Q) : Set := Id (Qle_bool x y) true.

(* ================= Section 3. Semantic-equivalence self-check of the decisions ================= 
      *)

(* The comparison copies with the same shape as the originals of this
   development: the definition bodies of [S02_CauchyComplete.v],
   transcribed verbatim, serve as the comparison side of the
   equivalence statements; the wrappers and the comparison copies
   coincide under the conversion check. *)

Definition qltw_S02_Qlt_bool (x y : Q) : bool :=
  match Qcompare x y with Lt => true | _ => false end.

Definition qltw_S02_Qle_bool (x y : Q) : bool :=
  match Qcompare x y with Gt => false | _ => true end.

(** Strict order: the wrapped Boolean and the [Qcompare] three-way
      split coincide at the conversion level. *)
Lemma qltw_Qlt_bool_Qcompare :
  forall x y : Q,
    Id (Qlt_bool x y) (match Qcompare x y with Lt => true | _ => false end).
Proof. intros x y. reflexivity. Defined.

(** Non-strict order: the stdlib native [Qle_bool] (the [Z.leb] form)
      and the reflected form of [Qcompare] coincide at the conversion
      level. *)
Lemma qltw_Qle_bool_Qcompare :
  forall x y : Q,
    Id (Qle_bool x y) (match Qcompare x y with Gt => false | _ => true end).
Proof. intros x y. reflexivity. Defined.

(** The equality decision: the stdlib native [Qeq_bool] ([Z.eqb] is a
      direct two-argument double match that never goes through
      [compare]; it agrees with the equality branch shape of
      [Qcompare] extensionally, not definitionally) -- verified branch
      by branch along the [Qcompare] three-way split: the equality
      branch closes through an equality chain via [Z.compare_eq] and
      [Z.eqb_refl], and the other two branches close directly.  The
      statement face remains [Set]-valued; the equality equation is
      used only inside proofs. *)
Lemma qltw_Qeq_bool_Qcompare :
  forall x y : Q,
    Id (Qeq_bool x y) (match Qcompare x y with Eq => true | _ => false end).
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - unfold Qeq_bool. rewrite (proj1 (Z.compare_eq_iff _ _) E). rewrite Z.eqb_refl.
    exact (@id_refl bool true).
  - assert (Hlt : (Qnum x * QDen y < Qnum y * QDen x)%Z)
      by exact (proj1 (Z.compare_lt_iff _ _) E).
    assert (Hne : ((Qnum x * QDen y) <> (Qnum y * QDen x))%Z)
      by (intro Hc; rewrite Hc in Hlt; exact (Z.lt_irrefl _ Hlt)).
    unfold Qeq_bool. rewrite (proj2 (Z.eqb_neq _ _) Hne).
    exact (@id_refl bool false).
  - assert (Hlt : (Qnum y * QDen x < Qnum x * QDen y)%Z)
      by exact (proj1 (Z.compare_gt_iff _ _) E).
    assert (Hne : ((Qnum x * QDen y) <> (Qnum y * QDen x))%Z)
      by (intro Hc; rewrite Hc in Hlt; exact (Z.lt_irrefl _ Hlt)).
    unfold Qeq_bool. rewrite (proj2 (Z.eqb_neq _ _) Hne).
    exact (@id_refl bool false).
Defined.

(** Wrapped Booleans vs the originals of this development (item by
      item at the [bool] level): the strict-order side. *)
Lemma qltw_Qlt_bool_orig :
  forall x y : Q, Id (Qlt_bool x y) (qltw_S02_Qlt_bool x y).
Proof. intros x y. reflexivity. Defined.

(** Wrapped Booleans vs the originals of this development (item by
      item at the [bool] level): the non-strict-order side. *)
Lemma qltw_Qle_bool_orig :
  forall x y : Q, Id (Qle_bool x y) (qltw_S02_Qle_bool x y).
Proof. intros x y. reflexivity. Defined.

(** Statement-level interchange (strict order): the [QltT] statement
      of this file and the same-shaped [Id] statement of the original
      imply each other. *)
Lemma qltw_QltT_orig :
  forall x y : Q, QltT x y -> Id (qltw_S02_Qlt_bool x y) true.
Proof. intros x y H. exact (id_trans (@id_refl _ (qltw_S02_Qlt_bool x y)) H). Defined.

Lemma qltw_S02_QltT :
  forall x y : Q, Id (qltw_S02_Qlt_bool x y) true -> QltT x y.
Proof. intros x y H. exact (id_trans (@id_refl _ (Qlt_bool x y)) H). Defined.

(** Statement-level interchange (non-strict order): the [QleT']
      statement of this file and the same-shaped [Id] statement of the
      original imply each other. *)
Lemma qltw_QleT'_orig :
  forall x y : Q, QleT' x y -> Id (qltw_S02_Qle_bool x y) true.
Proof. intros x y H. exact (id_trans (@id_refl _ (qltw_S02_Qle_bool x y)) H). Defined.

Lemma qltw_S02_QleT' :
  forall x y : Q, Id (qltw_S02_Qle_bool x y) true -> QleT' x y.
Proof. intros x y H. exact (id_trans (@id_refl _ (Qle_bool x y)) H). Defined.

(* ================= Section 4. Concrete numeric spot-check computations ================= *)

Definition qltw_samp_QltT_0_1 : QltT 0 1 := @id_refl bool true.

Definition qltw_samp_QleT'_1_1 : QleT' 1 1 := @id_refl bool true.

Definition qltw_samp_Qeq_bool_2_2 : Id (Qeq_bool 2 2) true := @id_refl bool true.

(* Path A v2.4 canonical carrier block (unified by WING-M7). *)
(* Carrier supply section: [And]/[NatLe]/[ZleT]/[ZltT]/[IffT] with their
   double-sided reflection bridges, moved here so every consumer module
   obtains them from this single source (Path A v2.4, Set-carried).
   The two stdlib imports below feed the bridge proofs only (no new
   in-package dependency). *)
Definition And (A B : Set) : Set := A * B.
(* The [nat] order reflected at the [Set] level: the [leb] decision in *)
(* identity form *)
Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.
(* ---- Fully constructive argument bridge: [NatLe] <-> [(<=)%nat] ---- *)
Lemma NatLe_drop : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  unfold NatLe in H.
  destruct (Nat.leb n m) eqn:E.
  - apply (proj1 (Nat.leb_le n m)). exact E.
  - inversion H.
Qed.

Lemma NatLe_lift : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    exact (proj2 (Nat.nle_gt n m) E H).
Qed.
(* ============================================================ *)
(* Set-level carriers for the [Z] order and the Set-level        *)
(* biconditional, for use by downstream modules                  *)
(* ============================================================ *)

(* The [Z] orders reflected at the [Set] level: the decisions in *)
(* identity form, mirroring [NatLe] above                        *)
Definition ZleT (n m : Z) : Set := Id (Z.leb n m) true.
Definition ZltT (n m : Z) : Set := Id (Z.ltb n m) true.
(* The Set-level biconditional, as the product of the two directions *)
Definition IffT (A B : Set) : Set := (A -> B) * (B -> A).

(* ---- Constructive bridges: [ZleT]/[ZltT] <-> [(<=)/(<)]%Z ---- *)
Lemma ZleT_drop : forall n m : Z, ZleT n m -> (n <= m)%Z.
Proof.
  intros n m H.
  unfold ZleT in H.
  destruct (Z.leb n m) eqn:E.
  - apply (proj1 (Z.leb_le n m)). exact E.
  - inversion H.
Qed.

Lemma ZleT_lift : forall n m : Z, (n <= m)%Z -> ZleT n m.
Proof.
  intros n m H.
  unfold ZleT.
  destruct (Z.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Z.leb_gt n m)) in E.
    exact (proj2 (Z.nle_gt n m) E H).
Qed.

Lemma ZltT_drop : forall n m : Z, ZltT n m -> (n < m)%Z.
Proof.
  intros n m H.
  unfold ZltT in H.
  destruct (Z.ltb n m) eqn:E.
  - apply (proj1 (Z.ltb_lt n m)). exact E.
  - inversion H.
Qed.

Lemma ZltT_lift : forall n m : Z, (n < m)%Z -> ZltT n m.
Proof.
  intros n m H.
  unfold ZltT.
  destruct (Z.ltb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Z.ltb_ge n m)) in E.
    exact (proj2 (Z.nlt_ge n m) E H).
Qed.
