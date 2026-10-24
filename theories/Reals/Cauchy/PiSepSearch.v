(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiSepSearch: generic bounded search for the least
      separating index, with the separator as an explicit argument.

    Mission.  This file formalizes a bounded linear search
      [nsep_find] with an abstract Boolean separator
      [dec : Q -> nat -> bool] as an explicit argument: starting
      from [n] it tests [dec] stage by stage, returns the first
      separating index, and returns the budget endpoint when the
      fuel runs out.  The package: the upper bound [nsep_find_ub], the hit
      characterization [nsep_find_hit], minimality [nsep_find_min],
      the budgeted run [nsep_first] with its four corollaries
      [nsep_first_bound], [nsep_first_hit], [nsep_first_least] and
      [nsep_first_minimal].  Every conclusion holds for an
      arbitrary separator and budget; the [pi]-side instance is the
      window separator of [LW5SepComplexity]; a sqrt(2) Newton
      instance follows.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [Extraction]; from this development [PiCompareT] (the
      [Set]-valued identity [Id] with [id_refl]) and [PiWindowCore]
      (the bridges [leiblw_id_eq], [leiblw_id_inv]).  The
      conjunction face of [nsep_find_hit] is the plain product type
      in the type scope (the shape of the [And] wrapper of
      [PiKernelSlack], not imported here).

    References.  This development, [NsepFindGeneric.v], the
      upstream module carried over here statement by statement:
      the fixed search [lw5n_find] of [LW5SepComplexity.v] with
      the separator lifted to an explicit argument, package
      [lw5n_find_ub], [lw5n_find_hit], [lw5n_find_min],
      [lw5n_nsep_bound], [lw5n_nsep_hit], [lw5n_nsep_least],
      [lw5n_nsep_minimal]; the bridges and the identity [Id] as in
      [PiWindowCore.v] and [PiCompareT.v]; the sqrt(2) instance
      follows the [is3] Newton family of [UpReqSqrt3Irrational.v].

    Constructivity.  Assumption-free and fully proved;
      conclusions at the [Set] level ([Id] and the product type);
      [nat] order occurs in premises and in the upper bounds
      [nsep_find_ub], [nsep_first_bound] and [nsep_first_least];
      [nsep_find] is structurally recursive and extractable.

    Build.  [rocq c -native-compiler no -q -Q theories pi_leibniz
      -Q theories/Reals/Cauchy ""
      theories/Reals/Cauchy/PiSepSearch.v] from the repository
      root compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import PiCompareT.
Require Import PiWindowCore.

(* ============ Section 1. The generic bounded linear search ============ *)

(** The search [nsep_find] tests the separator [dec] stage by stage
    from [n]; on a hit it returns that stage, and when the fuel runs
    out it returns the budget endpoint [n + fuel] without claiming a
    hit.  Every statement of this section holds for an arbitrary
    separator [dec : Q -> nat -> bool]. *)
Fixpoint nsep_find (dec : Q -> nat -> bool) (q : Q) (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | Datatypes.S f =>
      if dec q n then n else nsep_find dec q (Datatypes.S n) f
  end.

(** Search upper bound: the search never passes the starting index
    plus the fuel. *)
Lemma nsep_find_ub : forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  (nsep_find dec q n fuel <= n + fuel)%nat.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n.
  - simpl. lia.
  - simpl. destruct (dec q n).
    + lia.
    + specialize (IH (Datatypes.S n)). lia.
Qed.

(** Hit characterization: if some stage [n0] of the window
    [n, n + fuel] separates (i.e. [dec q n0] is [true]), then the
    search stops at a separating stage (first conjunct) and never
    passes [n0] (second conjunct).  Both conclusions are carried at
    the [Set] level: the Boolean equalities as [Id], the conjunction
    as the product type. *)
Lemma nsep_find_hit : forall (dec : Q -> nat -> bool) (q : Q) (fuel n n0 : nat),
  (n <= n0)%nat -> (n0 <= n + fuel)%nat ->
  Id (dec q n0) true ->
  (Id (dec q (nsep_find dec q n fuel)) true *
      Id (Nat.leb (nsep_find dec q n fuel) n0) true)%type.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n n0 Hn1 Hn2 Hhit.
  - assert (Heq : n = n0) by lia. subst n0. simpl.
    split; [exact Hhit|].
    apply leiblw_id_eq. apply Nat.leb_le. lia.
  - simpl. destruct (dec q n) eqn:E.
    + split.
      * rewrite E. apply id_refl.
      * apply leiblw_id_eq. apply Nat.leb_le. lia.
    + apply (IH (Datatypes.S n) n0).
      * destruct (Nat.eq_dec n n0) as [Heq|Hne].
        -- subst n0. apply leiblw_id_inv in Hhit. rewrite E in Hhit.
           discriminate Hhit.
        -- lia.
      * lia.
      * exact Hhit.
Qed.

(** Minimality: every stage [m] below the stopping point of the
    search fails to separate ([dec q m] is [false], carried as
    [Id]). *)
Lemma nsep_find_min : forall (dec : Q -> nat -> bool) (q : Q) (fuel n m : nat),
  (n <= m)%nat -> (m < nsep_find dec q n fuel)%nat ->
  Id (dec q m) false.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n m Hn1 Hlt.
  - simpl in Hlt. lia.
  - simpl. destruct (dec q n) eqn:E.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt. lia.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt.
      destruct (Nat.eq_dec n m) as [Heq|Hne].
      * subst m. rewrite E. apply id_refl.
      * apply (IH (Datatypes.S n) m); lia.
Qed.

(* ========== Section 2. The budgeted run and its characterization ========== *)

(** The budgeted run [nsep_first dec b q] is the search started at 0
    with budget [b].  The four corollaries mirror the fixed-separator
    package of [LW5SepComplexity] statement by statement, with the
    budget [b] explicit. *)
Definition nsep_first (dec : Q -> nat -> bool) (b : nat) (q : Q) : nat :=
  nsep_find dec q 0 b.

(** Run upper bound: the budgeted run never passes the budget [b]. *)
Theorem nsep_first_bound : forall (dec : Q -> nat -> bool) (b : nat) (q : Q),
  (nsep_first dec b q <= b)%nat.
Proof.
  intros dec b q. unfold nsep_first.
  pose proof (nsep_find_ub dec q b 0) as H. lia.
Qed.

(** Hit theorem: if a separating stage lies within the budget, the
    budgeted run stops at a separating stage. *)
Theorem nsep_first_hit : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  Id (dec q n0) true ->
  Id (dec q (nsep_first dec b q)) true.
Proof.
  intros dec b q n0 Hb Hhit. unfold nsep_first.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [H _].
  exact H.
Qed.

(** No-passing theorem: the budgeted run never passes any separating
    stage within the budget. *)
Theorem nsep_first_least : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  Id (dec q n0) true ->
  (nsep_first dec b q <= n0)%nat.
Proof.
  intros dec b q n0 Hb Hhit.
  apply Nat.leb_le. apply leiblw_id_inv.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [_ H].
  exact H.
Qed.

(** Minimality characterization: the least separating stage within
    the budget is taken verbatim by the budgeted run; from a
    separating stage [n0] with no separating stage below it, the run
    equals [n0] as a [Set]-level identity. *)
Theorem nsep_first_minimal : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  Id (dec q n0) true ->
  (forall m : nat, (m < n0)%nat -> Id (dec q m) false) ->
  Id (nsep_first dec b q) n0.
Proof.
  intros dec b q n0 Hb Hn Hmin.
  assert (Hhit := nsep_first_hit dec b q n0 Hb Hn).
  assert (Hle := nsep_first_least dec b q n0 Hb Hn).
  destruct (Nat.eq_dec (nsep_first dec b q) n0) as [E|E].
  - rewrite E. apply id_refl.
  - exfalso.
    assert (Hlt : (nsep_first dec b q < n0)%nat) by lia.
    specialize (Hmin _ Hlt).
    assert (Ht : dec q (nsep_first dec b q) = true)
      by (apply leiblw_id_inv; exact Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Qed.

(* =========== Section 3. Instance: the sqrt(2) Newton separator =========== *)

(** The iteration [x_0 = 2], [x_{n+1} = (x_n + 2/x_n) * (1/2)]; the
    square error is [delta_n = x_n^2 - 2] and the window width is
    [e_n = (1/2) * delta_n].  At stage [n] the separator [ir2_sep_dec]
    asks whether [q] has escaped the window [e_n] around [x_n] (the
    negation of the non-strict window test, the same shape as the
    window separator of [LW5SepComplexity]). *)
Fixpoint ir2_x (n : nat) : Q :=
  match n with
  | 0%nat => 2%Q
  | Datatypes.S m => (ir2_x m + 2%Q / ir2_x m) * (1 # 2)
  end.

Definition ir2_delta (n : nat) : Q := ir2_x n * ir2_x n - 2%Q.
Definition ir2_e (n : nat) : Q := (1 # 2) * ir2_delta n.

Definition ir2_sep_dec (q : Q) (n : nat) : bool :=
  negb (Qle_bool (Qabs ((q - ir2_x n)%Q)) (ir2_e n)).

(** Instance type face: [ir2_sep_dec] fits the separator argument
    shape of [nsep_find]. *)
Check (ir2_sep_dec : Q -> nat -> bool).
Check (nsep_find ir2_sep_dec : Q -> nat -> nat -> nat).

(* ========== Section 4. Computational spot checks and audit ========== *)

(** For the sample [q = 3/2]: at stage 0 one has [x_0 = 2] and
    [e_0 = 1], so [abs(3/2 - 2) = 1/2] stays inside the window and
    [dec(0)] is [false]; at stage 2 one has [x_2 = 17/12] and
    [e_2 = 1/288], so [abs(3/2 - 17/12) = 1/12 > 1/288] and [dec(2)]
    is [true]; the least hit is at stage 2. *)
Eval vm_compute in (ir2_sep_dec (3 # 2) 0, ir2_sep_dec (3 # 2) 2).
Eval vm_compute in (ir2_sep_dec (3 # 2) 3).
Eval vm_compute in (nsep_find ir2_sep_dec (3 # 2) 0 10).

Separate Extraction nsep_find nsep_first ir2_sep_dec ir2_x ir2_e ir2_delta.

Print Assumptions nsep_find_ub.
Print Assumptions nsep_find_hit.
Print Assumptions nsep_find_min.
Print Assumptions nsep_first_bound.
Print Assumptions nsep_first_hit.
Print Assumptions nsep_first_least.
Print Assumptions nsep_first_minimal.
