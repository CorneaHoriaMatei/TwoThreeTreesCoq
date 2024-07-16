Require Import Nat.
Require Import List.
Import ListNotations.
Require Import TTtree.TTtreeDatatypes.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.



(* bdestruct tactic copy pasted from VFA*)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

#[local]Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct_gen X H :=
  let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestruct_gen X H.
Tactic Notation "bdestruct" constr(X) :=
  let H := fresh in bdestruct_gen X H.

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  | |- context [ if (?X =? ?Y) || _ then _ else _ ] => bdestruct (X =? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; subst; auto).

(* =================== Invariants =================== *)

Fixpoint ForallTTtree (P : nat -> Prop) (t : TTtree) : Prop :=
  match t with
  | Empty => True
  | Node2 l v r => P v /\ ForallTTtree P l /\ ForallTTtree P r
  | Node3 l v1 m v2 r => P v1 /\ P v2 /\ ForallTTtree P l /\ ForallTTtree P m /\ ForallTTtree P r
  end
.

Inductive ordered : TTtree -> Prop :=
  | orderedEmpty : ordered Empty
  | orderedNode2 : forall l v r,
      ForallTTtree (fun x => x < v) l ->
      ForallTTtree (fun x => x > v) r ->
      ordered l ->
      ordered r ->
      ordered (Node2 l v r)
  | orderedNode3 : forall l v1 m v2 r,
      v1 < v2 ->
      ForallTTtree (fun x => x < v1) l ->
      ForallTTtree (fun x => x > v1 /\ x < v2) m ->
      ForallTTtree (fun x => x > v2) r ->
      ordered l ->
      ordered m ->
      ordered r ->
      ordered (Node3 l v1 m v2 r)
.

Fixpoint height (t : TTtree) : nat :=
  match t with
  | Empty => 0
  | Node2 l _ r => 1 + max (height l) (height r)
  | Node3 l _ m _ r => 1 + max (height l) (max (height m) (height r))
  end
.

Inductive balanced : TTtree -> Prop :=
  | balancedEmpty : balanced Empty
  | balancedNode2 : forall l r v,
      balanced l ->
      balanced r ->
      height l = height r ->
      balanced (Node2 l v r)
  | balancedNode3 : forall l m r v1 v2,
      balanced l ->
      balanced m ->
      balanced r ->
      height l = height m ->
      height m = height r ->
      balanced (Node3 l v1 m v2 r)
.

Definition isTTtree (t : TTtree) : Prop :=
  ordered t /\ balanced t
.

(* =================== Helper lemmas =================== *)

Lemma ForallTTtreeSplit : forall (value1 value2 : nat) (tree : TTtree),
  ForallTTtree (fun x : nat => x > value1 /\ x < value2) tree <->
  ForallTTtree (fun x : nat => x > value1) tree /\ ForallTTtree (fun x : nat => x < value2) tree.
Proof.
  intros value1 value2 tree.
  split.
  - (* -> direction *)
    induction tree as [| l IHl v r IHr | l IHl v1 m IHm v2 r IHr]; simpl; intros H.

    + (* Case: tree = Empty *)
      split; simpl; trivial.

    + (* Case: tree = Node2 l v r *)
      simpl in H. destruct H as [Hv [Hl Hr]].
      split.
      * split.
        -- apply Hv.
        -- split; [apply IHl | apply IHr]; assumption.
      * split.
        -- apply Hv.
        -- split; [apply IHl | apply IHr]; assumption.

    + (* Case: tree = Node3 l v1 m v2 r *)
      simpl in H. destruct H as [Hv1 [Hv2 [Hl [Hm Hr]]]].
      split.
      * split.
        -- apply Hv1.
        -- split.
           ++ apply Hv2.
           ++ split; [apply IHl | split; [apply IHm | apply IHr]]; assumption.
      * split.
        -- apply Hv1.
        -- split.
           ++ apply Hv2.
           ++ split; [apply IHl | split; [apply IHm | apply IHr]]; assumption.
  - (* <- direction *)
    induction tree as [| l IHl v r IHr | l IHl v1 m IHm v2 r IHr]; simpl; intros [H1 H2].

    + (* Case: tree = Empty *)
      simpl. trivial.

    + (* Case: tree = Node2 l v r *)
      simpl in H1, H2. destruct H1 as [Hv1 [Hl1 Hr1]]. destruct H2 as [Hv2 [Hl2 Hr2]].
      simpl. split.
      * lia.
      * split; [apply IHl | apply IHr]; split; assumption.

    + (* Case: tree = Node3 l v1 m v2 r *)
      simpl in H1, H2. destruct H1 as [Hv1 [Hv2 [Hl1 [Hm1 Hr1]]]].
      destruct H2 as [Hv3 [Hv4 [Hl2 [Hm2 Hr2]]]].
      simpl. split.
      * lia.
      * split.
        -- lia.
        -- split; [apply IHl | split; [apply IHm | apply IHr]]; split; assumption.
Qed.

Lemma ForallTTtreeTrans : forall (P Q : nat -> Prop) (t : TTtree),
  ForallTTtree P t ->
  (forall x, P x -> Q x) ->
  ForallTTtree Q t.
Proof.
  intros P Q t HForall HPQ.
  induction t as [| l IHl v r IHr | l IHl v1 m IHm v2 r IHr]; simpl in *.

  - (* Case: t = Empty *)
    constructor.

  - (* Case: t = Node2 l v r *)
    destruct HForall as [Hv [HForallL HForallR]].
    split.
    + apply HPQ. assumption.
    + split.
      * apply IHl. assumption.
      * apply IHr. assumption.

  - (* Case: t = Node3 l v1 m v2 r *)
    destruct HForall as [Hv1 [Hv2 [HForallL [HForallM HForallR]]]].
    split.
    + apply HPQ. assumption.
    + split.
      * apply HPQ. assumption.
      * split.
        -- apply IHl. assumption.
        -- split.
           ++ apply IHm. assumption.
           ++ apply IHr. assumption.
Qed.

Lemma ForallTTtreeUpward : forall (P : nat -> Prop) (v : nat) (t : TTtree),
  P v ->
  ForallTTtree P t ->
  ForallTTtree P (convertRootKickUp(upward v t)).
Proof.
  intros P v t Hp HForall.
  induction t as [| l IHl value r IHr | l IHl value1 m IHm value2 r IHr].

  - (* Case: t = Empty *)
    simpl. auto.

  - (* Case: t = Node2 l value r *)
    simpl.
    bdestruct (v<?value) as Hlessvalue.

    * (* v < value *)
      destruct (upward v l) eqn:HupL.
      -- (* upward v l = Normal t *)
         simpl in HForall. destruct HForall as [H1 [H2 H3]]. repeat split; try assumption.
         simpl in IHl. apply IHl. auto.
      -- (* upward v l = KickUp l0 v0 r0 *)
         simpl. simpl in HForall. destruct HForall. destruct H0. repeat split; try assumption.
         simpl in IHl.
         ** apply IHl. assumption.
         ** apply IHl. assumption.
         ** apply IHl. assumption.

    * (* v >= value *)
      destruct (upward v r) eqn:HupR.
      -- (* upward v r = Normal t *)
         simpl in *. repeat split; try apply HForall. apply IHr. apply HForall.
      -- (* upward v r = KickUp l0 v0 r0 *)
         simpl in *. repeat split; try apply HForall.
         ** apply IHr. apply HForall.
         ** apply IHr. apply HForall.
         ** apply IHr. apply HForall.

  - (* Case: t = Node3 l value1 m value2 r *)
    simpl.
    bdestruct (v<?value1) as Hvalue1.

    * (* v < value1 *)
      destruct (upward v l) eqn:HupL.
      -- (* upward v l = Normal t *)
         simpl in *. repeat split; try apply HForall. apply IHl. apply HForall.
      -- (* upward v l = KickUp l0 v0 r0 *)
         simpl in *. repeat split; try apply HForall.
         ** apply IHl. apply HForall.
         ** apply IHl. apply HForall.
         ** apply IHl. apply HForall.
    * (* v >= value1 *)
      bdestruct (value2<?v) as Hvalue2.
      -- (* v > value2 *)
         destruct (upward v r) eqn:HupL.
         ** (* upward v r = Normal t *)
            simpl in *. repeat split; try apply HForall. apply IHr. apply HForall.
         ** (* upward v r = KickUp l0 v0 r0 *)
            simpl in *. repeat split; try apply HForall.
            + apply IHr. apply HForall.
            + apply IHr. apply HForall.
            + apply IHr. apply HForall.
      -- (* v <= value2 *)
         destruct (upward v m) eqn:HupM.
         ** (* upward v m = Normal t *)
            simpl in *. repeat split; try apply HForall. apply IHm. apply HForall.
         ** (* upward v m = KickUp l0 v0 r0 *)
            simpl in *. repeat split; try apply HForall; try apply IHm; apply HForall.
Qed.

Lemma ForallTTtreeLookup : forall P t x,
  ForallTTtree P t ->
  lookup x t = true ->
  P x.
Proof.
  intros P t x HForall HLookup.
  induction t as [| l IHl value r IHr | l IHl value1 m IHm value2 r IHr].

  -- (* Case: t = Empty *)
     simpl in *. discriminate HLookup.

  -- (* Case: t = Node2 l value r *)
     simpl in *. bdestruct (x=?value).
     + (* x = value *)
       subst. apply HForall.
     + (* x <> value *)
       bdestruct (x<?value).
       ++ (* x < value *)
          apply IHl; try apply HForall; try apply HLookup.
       ++ (* x > value *)
          apply IHr; try apply HForall; try apply HLookup.

  -- (* Case: t = Node3 l value1 m value2 r *)
     simpl in *. bdestruct (x=?value1) as Hvalue1.
     + (* x = value1 *)
       subst. apply HForall.
     + bdestruct (x=?value2) as HValue2.
       ++ (* x = value2 *)
          subst. apply HForall.
       ++ (* x = value *)
          bdestruct (x<?value1).
          * (* x < value1 *)
            simpl in *. apply IHl. repeat split; try apply HForall. apply HLookup.
          * (* x > value1 *)
            bdestruct (value2<?x).
            ** (* x > value2 *)
               simpl in *. apply IHr. repeat split; try apply HForall. apply HLookup.
            ** (* x < value2 *)
               simpl in *. apply IHm. repeat split; try apply HForall. apply HLookup.
Qed.

Lemma lookupNode2False : forall (x value : nat) (l r : TTtree),
  ordered (Node2 l value r) ->
  lookup x (Node2 l value r) = false ->
  lookup x l = false /\ lookup x r = false /\ x <> value.
Proof.
  intros x value l r Hordered Hlookup.
  simpl in Hlookup.
  bdestruct (x =? value) as Heq.
  - (* Case: x = value *)
    discriminate Hlookup.
  - (* Case: x <> value *)
    bdestruct (x <? value) as Hlt.
    + (* Case: x < value *)
      simpl in Hlookup. split.
      * assumption.
      * split.
        ** inversion Hordered.
           destruct (lookup x r) eqn:HlookR.
           -- apply ForallTTtreeLookup with (x:=x) in H3.
              ++ lia.
              ++ assumption.
           -- reflexivity.
        ** assumption.
    + (* Case: x > value *)
      split.
      * destruct (lookup x l) eqn:HLookL.
        ** inversion Hordered.
           apply ForallTTtreeLookup with (x:=x) in H2.
           -- lia.
           -- assumption.
        ** reflexivity.
      * split.
        ** assumption.
        ** assumption.
Qed.

Lemma lookupNode3False : forall (x v1 v2 : nat) (l m r : TTtree),
  ordered (Node3 l v1 m v2 r) ->
  lookup x (Node3 l v1 m v2 r) = false ->
  lookup x l = false /\ lookup x m = false /\ lookup x r = false /\ x <> v1 /\ x <> v2.
Proof.
  intros x v1 v2 l m r Hordered Hlookup.
  simpl in Hlookup.
  bdestruct (x =? v1) as Heq1.
  - (* x = v1 *)
    discriminate Hlookup.
  - (* x <> v1 *)
    bdestruct (x =? v2) as Heq2.
    + (* x = v2 *)
      discriminate Hlookup.
    + (* x <> v1 *)
      bdestruct (x <? v1) as Hlt1.
      * (* x < v1 *)
        simpl in Hlookup. repeat split; try assumption.
        -- inversion Hordered.
           destruct (lookup x m) eqn:HlookupM.
           ++ apply ForallTTtreeSplit in H6. destruct H6 as [H6left H6right].
              apply ForallTTtreeLookup with (x:=x) in H6left.
              ** lia.
              ** assumption.
           ++ reflexivity.
        -- inversion Hordered.
           destruct (lookup x r) eqn:HlookupR.
           ++ apply ForallTTtreeLookup with (x:=x) in H7.
              ** lia.
              ** assumption.
           ++ reflexivity.
      * (* x > v1 *)
        bdestruct (v2 <? x) as Hlt2.
        -- (* x > v2 *)
           simpl in Hlookup.
           repeat split; try assumption.
           ++ destruct (lookup x l) eqn:HlookupL.
              ** inversion Hordered.
                 apply ForallTTtreeLookup with (x:=x) in H5.
                 --- lia.
                 --- assumption.
              ** reflexivity.
           ++ destruct (lookup x m) eqn:HlookupM.
              ** inversion Hordered.
                 apply ForallTTtreeSplit in H6. destruct H6 as [H6left H6right].
                 apply ForallTTtreeLookup with (x:=x) in H6right.
                 --- lia.
                 --- assumption.
              ** reflexivity.
        -- (* x < v2 *)
           simpl in Hlookup.
           repeat split; try assumption.
           ++ destruct (lookup x l) eqn:HlookupL.
              ** inversion Hordered.
                 apply ForallTTtreeLookup with (x:=x) in H5.
                 --- lia.
                 --- assumption.
              ** reflexivity.
           ++ destruct (lookup x r) eqn:HlookupR.
              ** inversion Hordered.
                 apply ForallTTtreeLookup with (x:=x) in H7.
                 --- lia.
                 --- assumption.
              ** reflexivity.
Qed.

(* =================== Invariant maintenance for insertion =================== *)

Lemma orderedLookupFalseInsert: forall (tree : TTtree) (v : nat),
  ordered tree ->
  lookup v tree = false ->
  ordered (convertRootKickUp (upward v tree)).
Proof.
  intros tree v Hordered Hlookup.
  induction tree as [| l IHl value r IHr | l IHl value1 m IHm value2 r IHr].

  - (* Case: tree = Empty *)
    simpl. constructor.
    * simpl. trivial.
    * simpl. trivial.
    * assumption.
    * assumption.

  - (* Case: tree = Node2 l value r *)
    simpl in *.
    unfold convertRootKickUp.
    bdestruct (v =? value) as Hvalue.
    * (* v = value *)
      discriminate Hlookup.
    * (* v <> value *)
      bdestruct (v <? value) as Hlt.
      + (* v < value *)
        destruct (upward v l) eqn:Hup.
        -- (* upward v l = Normal t *)
          simpl in *. inversion Hordered.
          constructor; try assumption.
          ** apply ForallTTtreeUpward with (v:=v) in H2.
             rewrite Hup in H2. simpl in H2.
             ++ assumption.
             ++ assumption.
          ** apply IHl.
             ++ assumption.
             ++ auto.
        -- (* upward v l = KickUp l0 v0 r0 *)
          simpl in *. inversion Hordered.
          specialize (IHl H4 Hlookup).
          inversion IHl.
          apply ForallTTtreeUpward with (v:=v) in H2.
          rewrite Hup in H2. simpl in H2.
          destruct H2 as [Hv [Hl0 Hr0]].
          constructor; try assumption.
          ** apply ForallTTtreeSplit. auto.
          ** assumption.
      + (* v > value *)
        destruct (upward v r) eqn:Hup.
        -- (* upward v r = Normal t *)
          simpl in *. inversion Hordered.
          constructor; try assumption.
          ** apply ForallTTtreeUpward with (v:=v) in H3.
             rewrite Hup in H3. simpl in H3.
             ++ assumption.
             ++ lia.
          ** apply IHr.
             ++ assumption.
             ++ assumption.
        -- (* upward v r = KickUp l0 v0 r0 *)
          simpl in *. inversion Hordered. 
          specialize (IHr H5 Hlookup).
          inversion IHr.
          apply ForallTTtreeUpward with (v:=v) in H3.
          rewrite Hup in H3. simpl in H3.
          constructor; try assumption.
          ** lia.
          ** destruct H3 as [Hv [Hl0 Hr0]]. apply ForallTTtreeSplit. auto.
          ** lia.

  - (* Case: tree = Node3 l value1 m value2 r *)
    simpl.
    unfold convertRootKickUp.
    bdestruct (v <? value1) as Hlt1.
    * (* v < value1 *)
      destruct (upward v l) eqn:Hup.
      + (* upward v l = Normal t *)
        simpl. inversion Hordered.
        constructor; try assumption.
        -- apply ForallTTtreeUpward with (v:=v) in H5.
           rewrite Hup in H5. simpl in H5.
           ** assumption.
           ** assumption.
        -- simpl in IHl.
           apply IHl.
           ** assumption.
           ** apply lookupNode3False in Hlookup.
              destruct Hlookup as [HlookL HlookMid].
              ++ apply HlookL.
              ++ assumption.
      + (* upward v l = KickUp l0 v0 r0 *)
        inversion Hordered. simpl in IHl.
        apply lookupNode3False in Hlookup.
        -- destruct Hlookup as [HlookL [HlookM [HlookR [Hvalue1 Hvalue2]]]].
           specialize (IHl H8 HlookL).
           constructor; try assumption.
           inversion IHl.
           ** apply ForallTTtreeUpward with (v:=v) in H5.
              rewrite Hup in H5. simpl in H5.
              destruct H5.
              constructor; try assumption.
              assumption.
           ** constructor; try assumption.
              split.
              ++ apply ForallTTtreeSplit in H6. destruct H6. assumption.
              ++ apply ForallTTtreeTrans with (P:=fun x : nat => x > value2).
                 --- assumption.
                 --- lia.
           ** constructor; try assumption.
              apply ForallTTtreeSplit in H6. destruct H6. assumption.
        -- assumption.
    * (* v >= value1 *)
      bdestruct (value2 <? v) as Hgt2.
      + (* v > value2 *)
        -- destruct (upward v r) eqn:Hup.
           ** (* upward v r = Normal t *)
              simpl. inversion Hordered.
              constructor; try assumption.
              ++ apply ForallTTtreeUpward with (v:=v) in H7.
                 rewrite Hup in H7. simpl in H7.
                 --- assumption.
                 --- assumption.
              ++ simpl in IHr.
                 apply IHr.
                 --- assumption.
                 --- apply lookupNode3False in Hlookup.
                     destruct Hlookup as [HlookL [HlookM [HlookR [Hvalue1 Hvalue2]]]].
                     *** apply HlookR.
                     *** assumption.
           ** (* upward v r = KickUp l0 v0 r0 *)
              inversion Hordered. simpl in IHr.
              apply lookupNode3False in Hlookup.
              ++ destruct Hlookup as [HlookL [HlookM [HlookR [Hvalue1 Hvalue2]]]].
                 specialize (IHr H10 HlookR).
                 constructor; try assumption.
                 inversion IHr.
                 --- apply ForallTTtreeUpward with (v:=v) in H7.
                     rewrite Hup in H7. simpl in H7.
                     destruct H7.
                     constructor; try assumption.
                     *** apply ForallTTtreeSplit in H6. destruct H6.
                         split.
                         +++ apply ForallTTtreeTrans with (P:=fun x : nat => x < value1).
                             **** assumption.
                             **** lia.
                         +++ assumption.
                     *** assumption.
                 --- constructor; try assumption.
                     *** apply ForallTTtreeSplit in H6. destruct H6.
                         apply ForallTTtreeUpward with (v:=v) in H7.
                         rewrite Hup in H7. simpl in H7. destruct H7.
                         +++ assumption.
                         +++ assumption.
                     *** apply ForallTTtreeSplit in H6. destruct H6.
                         apply ForallTTtreeUpward with (v:=v) in H7.
                         rewrite Hup in H7. simpl in H7. destruct H7.
                         +++ apply H12.
                         +++ assumption.
                 --- constructor; try assumption.
                     apply ForallTTtreeSplit in H6. destruct H6.
                     assumption.
              ++ assumption.
      + (* v <= value2 *)
        -- destruct (upward v m) eqn:Hup.
           ** (* upward v m = Normal t *)
              simpl. inversion Hordered.
              constructor; try assumption.
              ++ apply ForallTTtreeUpward with (v:=v) in H6.
                 rewrite Hup in H6. simpl in H6.
                 --- assumption.
                 --- apply lookupNode3False in Hlookup. split.
                     *** lia.
                     *** lia.
                     *** assumption.
              ++ simpl in IHr.
                 apply IHm.
                 --- assumption.
                 --- apply lookupNode3False in Hlookup.
                     destruct Hlookup as [HlookL [HlookM [HlookR [Hvalue1 Hvalue2]]]].
                     *** apply HlookM.
                     *** assumption.
           ** (* upward v m = KickUp l0 v0 r0 *)
              inversion Hordered. simpl in IHm.
              apply lookupNode3False in Hlookup.
              ++ destruct Hlookup as [HlookL [HlookM [HlookR [Hvalue1 Hvalue2]]]].
                 specialize (IHm H9 HlookM).
                 constructor; try assumption.
                 inversion IHm.
                 --- apply ForallTTtreeUpward with (v:=v) in H6.
                     rewrite Hup in H6. simpl in H6.
                     destruct H6.
                     constructor; try assumption.
                     *** lia.
                     *** split. destruct H6.
                         +++ apply ForallTTtreeTrans with (P:=fun x : nat => x < value1).
                             **** assumption.
                             **** lia.
                         +++ assumption.
                     *** lia.
                 --- constructor; try assumption.
                     *** apply ForallTTtreeSplit in H6. destruct H6.
                         apply ForallTTtreeUpward with (v:=v) in H11.
                         rewrite Hup in H11. simpl in H11. destruct H11.
                         +++ assumption.
                         +++ lia.
                     *** apply ForallTTtreeSplit in H6. destruct H6.
                         inversion IHm.
                         split.
                         **** assumption.
                         **** apply ForallTTtreeTrans with (P:=fun x : nat => x > value2).
                              { assumption. }
                              { apply ForallTTtreeUpward with (v:=v) in H11.
                                - rewrite Hup in H11. simpl in H11. destruct H11.
                                  lia.
                                - lia. }
                 --- apply ForallTTtreeSplit in H6. destruct H6.
                     inversion IHm.
                     constructor; try assumption.
                     apply ForallTTtreeUpward with (v:=v) in H6.
                     { rewrite Hup in H6. simpl in H6. destruct H6. apply H19. }
                     { lia. }
                 --- apply ForallTTtreeSplit in H6. destruct H6.
                     inversion IHm.
                     constructor; try assumption.
                     apply ForallTTtreeUpward with (v:=v) in H11.
                     { rewrite Hup in H11. simpl in H11. destruct H11. apply H19. }
                     { lia. }
              ++ assumption.
Qed.


Theorem orderedInsert : forall (tree : TTtree) (v : nat),
    ordered tree -> ordered (insert v tree).
Proof.
  intros tree v Hordered.
  unfold insert.
  destruct (lookup v tree) eqn:Hlookup.
  - (* lookup v tree = true *)
    assumption.
  - (* lookup v tree = false *)
    apply orderedLookupFalseInsert; try assumption.
Qed.

Lemma balancedUpwardKickup : forall tree v l v' r,
  balanced tree ->
  upward v tree = KickUp l v' r ->
  height tree = height l /\ height tree = height r /\ balanced l /\ balanced r.
Proof.
  intros tree v l' v' r' Hbalanced Hup.
  revert l' v' r' Hup.
  induction tree as [| left IHl v1 right IHr | l IHl v1 m IHm v2 r IHr]; intros l' v' r' Hup.

  - (* Case: tree = Empty *)
    simpl in *. inversion Hup.
    simpl. repeat split; auto.

  - (* Case: tree = Node2 left v1 right *)
    inversion Hbalanced. simpl in Hup. subst.
    bdestruct (v <? v1).
    + (* v < v1 *)
      destruct (upward v left) eqn:HupL; inversion Hup.
    + (* v >= v1 *)
      destruct (upward v right) eqn:HupL; inversion Hup.

  - (* Case: tree = Node3 l v1 m v2 r *)
    simpl in Hup.
    bdestruct (v <? v1).
    + (* v < v1 *)
      destruct (upward v l) eqn:HupL.
      * (* upward v l = Normal t *)
        inversion Hup.
      * (* upward v l = KickUp l0 v0 r0 *)
        inversion Hup; subst. simpl in *.
        inversion Hbalanced; subst; simpl.
        assert (height l = height l0 /\ height l = height r0 /\ balanced l0 /\ balanced r0) as [Hll0 [Hlr0 [Hball Hbalr]]].
        { eapply IHl; auto. }
        repeat split; try lia.
        -- constructor; auto; try lia.
        -- constructor; auto; try lia.
    + (* v >= v1 *)
      bdestruct (v2 <? v).
      * (* v > v2 *)
        destruct (upward v r) eqn:HupR.
        -- (* upward v r = Normal t *)
           discriminate Hup.
        -- (* upward v r = KickUp l0 v0 r0 *)
           inversion Hup. subst. simpl in *.
           inversion Hbalanced. subst.
           assert (height r = height l0 /\ height r = height r0 /\ balanced l0 /\ balanced r0) as [Hrl0 [Hrr0 [Hball Hbalr]]].
           { eapply IHr; auto. }
           repeat split; try lia.
           ++ constructor; auto; try lia.
           ++ constructor; auto; try lia.
      * (* v <= v2 *)
        destruct (upward v m) eqn:HupM.
        -- (* upward v m = Normal t *)
           discriminate Hup.
        -- (* upward v m = KickUp l0 v0 r0 *)
           inversion Hup. subst.
           inversion Hbalanced. subst.
           simpl in *.
           assert (height m = height l0 /\ height m = height r0 /\ balanced l0 /\ balanced r0) as [Hml0 [Hmr0 [Hball Hbalr]]].
           { eapply IHm; auto. }
           repeat split; try lia.
           ++ constructor; auto; try lia.
           ++ constructor; auto; try lia.
Qed.

Lemma balancedUpwardNormal : forall (tree t : TTtree) (v : nat),
  (balanced tree ->
  upward v tree = Normal t ->
  balanced t /\ height tree = height t).
Proof.
  intros tree t v Hbalanced Hup.
  generalize dependent t.
  induction tree as [| l IHl v1 r IHr | l IHl v1 m IHm v2 r IHr]; intros tree Hup.

  - (* Case: tree = Empty *)
    simpl in Hup. simpl in *. discriminate Hup.

  - (* Case: tree = Node2 l v1 r *)
    inversion Hbalanced. simpl in Hup. subst.
    bdestruct (v <? v1).
    + (* v < v1 *)
      destruct (upward v l) eqn:HupL.
      * (* upward v l = Normal t *)
        simpl in *. inversion Hup. simpl.
        assert (balanced t) as Hbalt0.
        { apply IHl; auto. }
        assert (height l = height t) as Hheight0.
        { apply IHl; auto. }
        split.
        -- constructor; auto. lia.
        -- rewrite Hheight0. reflexivity.
      * (* upward v l = KickUp l0 v0 r0 *)
        inversion Hup. subst.
        simpl.
        apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H2.
        destruct H2 as [Hll0 [Hlr0 [Hball Hbalr]]]. split.
        -- constructor; try assumption; try lia.
        -- lia.
        -- assumption.
    + (* v >= v1 *)
      destruct (upward v r) eqn:HupR.
      * (* upward v r = Normal t *)
        simpl in *. inversion Hup. simpl.
        assert (balanced t) as Hbalt0.
        { apply IHr; auto. }
        assert (height r = height t) as Hheight0.
        { apply IHr; auto. }
        split.
        -- constructor; auto. lia.
        -- rewrite Hheight0. reflexivity.
      * (* upward v r = KickUp l0 v0 r0 *)
        inversion Hup. subst.
        simpl.
        apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H3.
        destruct H3 as [Hrl0 [Hrr0 [Hball Hbalr]]]. split.
        -- constructor; try assumption; try lia.
        -- lia.
        -- assumption.

  - (* Case: tree = Node3 l v1 m v2 r *)
    inversion Hbalanced. simpl in *. subst.
    bdestruct (v <? v1).
    + (* v < v1 *)
      destruct (upward v l) eqn:HupL.
      * (* upward v l = Normal t *)
        inversion Hup. simpl.
        assert (balanced t) as Hbalt0.
        { apply IHl; auto. }
        assert (height l = height t) as Hheight0.
        { apply IHl; auto. }
        split.
        -- constructor; auto. lia.
        -- rewrite Hheight0. reflexivity.
      * (* upward v l = KickUp l0 v0 r0 *)
        discriminate Hup.
    + (* v >= v1 *)
      bdestruct (v2<?v).
      * (* v > v2 *)
        destruct (upward v r) eqn:HupR.
        -- (* upward v r = Normal t *)
           inversion Hup. simpl.
           assert (balanced t) as Hbalt0.
           { apply IHr; auto. }
           assert (height r = height t) as Hheight0.
           { apply IHr; auto. }
           split.
           ++ constructor; auto. lia.
           ++ rewrite Hheight0. reflexivity.
        -- (* upward v r = KickUp l0 v0 r0 *)
           discriminate Hup.
      * (* v <= v2 *)
        destruct (upward v m) eqn:HupM.
        -- (* upward v m = Normal t *)
           inversion Hup. simpl.
           assert (balanced t) as Hbalt0.
           { apply IHm; auto. }
           assert (height m = height t) as Hheight0.
           { apply IHm; auto. }
           split.
           ++ constructor; auto. lia. lia.
           ++ rewrite Hheight0. reflexivity.
        -- (* upward v m = KickUp l0 v0 r0 *)
           discriminate Hup.
Qed.

Theorem balancedInsert : forall (t : TTtree) (v : nat),
  balanced t -> balanced (insert v t).
Proof.
  intros t v Hbalanced.
  unfold insert.
  destruct (lookup v t) eqn:Hlookup.

  - (* Case: v is already in the tree *)
    assumption.

  - (* Case: v is not in the tree *)
    induction t as [| l IHl v1 r IHr | l IHl v1 m IHm v2 r IHr]; intros.

    + (* Case: t = Empty *)
      simpl. constructor; auto.

    + (* Case: t = Node2 l v1 r *)
      simpl.
      unfold convertRootKickUp.
      bdestruct (v <? v1).
      * (* v < v1 *)
        destruct (upward v l) eqn:Hup.
        -- (* upward v l = Normal t *)
           simpl in *. inversion Hbalanced.
           constructor; try assumption.
           ++ apply IHl. assumption. revert Hlookup. bdall.
           ++ apply balancedUpwardNormal with (tree:=l)(v:=v)(t:=t) in H3.
              ** lia.
              ** assumption.
        -- (* upward v l = KickUp l0 v0 r0 *)
           inversion Hbalanced.
           apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H3.
           destruct H3 as [Hll0 [Hlr0 [Hball Hbalr]]].
           ++ constructor; try assumption; try lia.
           ++ assumption.
      * (* v >= v1 *)
        destruct (upward v r) eqn:Hup.
        -- (* upward v r = Normal t *)
           simpl in *. inversion Hbalanced.
           constructor; try assumption.
           ++ apply IHr. assumption. revert Hlookup. bdall.
           ++ apply balancedUpwardNormal with (tree:=r)(v:=v)(t:=t) in H4.
              ** lia.
              ** assumption.
        -- (* upward v r = KickUp l0 v0 r0 *)
           inversion Hbalanced.
           apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H4.
           destruct H4 as [Hll0 [Hlr0 [Hball Hbalr]]].
           ++ constructor; try assumption; try lia.
           ++ assumption.

    + (* Case: t = Node3 l v1 m v2 r *)
      simpl.
      unfold convertRootKickUp.
      bdestruct (v <? v1).
      * (* v < v1 *)
        destruct (upward v l) eqn:Hup.
        -- (* upward v l = Normal t *)
           simpl in *. inversion Hbalanced.
           constructor; try assumption.
           ++ apply IHl. assumption. revert Hlookup. bdall.
           ++ apply balancedUpwardNormal with (tree:=l)(v:=v)(t:=t) in H5.
              ** lia.
              ** assumption.
        -- (* upward v l = KickUp l0 v0 r0 *)
           inversion Hbalanced.
           apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H5.
           destruct H5 as [Hll0 [Hlr0 [Hball Hbalr]]].
           ++ repeat constructor; try assumption; try lia. simpl. lia.
           ++ assumption.
      * (* v >= v1 *)
        bdestruct (v2 <? v).
        ++ (* v > v2 *)
           destruct (upward v r) eqn:Hup.
           ** (* upward v r = Normal t *)
              simpl in *. inversion Hbalanced.
              constructor; try assumption.
              { apply IHr. assumption. revert Hlookup. bdall. simpl. discriminate 1. }
              { apply balancedUpwardNormal with (tree:=r)(v:=v)(t:=t) in H8.
                - lia.
                - assumption. }
           ** (* upward v r = KickUp l0 v0 r0 *)
              inversion Hbalanced.
              apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H8.
              destruct H8 as [Hrl0 [Hrr0 [Hball Hbalr]]].
              { repeat constructor; try assumption; try lia. simpl. lia. }
              { assumption. }
        ++ (* v <= v2 *)
           destruct (upward v m) eqn:Hup.
           ** (* upward v m = Normal t *)
              simpl in *. inversion Hbalanced.
              constructor; try assumption.
              { apply IHm. assumption. revert Hlookup. bdall. simpl. discriminate 1. }
              { apply balancedUpwardNormal with (tree:=m)(v:=v)(t:=t) in H7.
                - lia.
                - assumption. }
              { apply balancedUpwardNormal with (tree:=m)(v:=v)(t:=t) in H7. lia. assumption. }
           ** (* upward v m = KickUp l0 v0 r0 *)
              inversion Hbalanced.
              apply balancedUpwardKickup with (v:=v)(l:=l0)(v':=v0)(r:=r0) in H7.
              destruct H7 as [Hrl0 [Hrr0 [Hball Hbalr]]].
              { repeat constructor; try assumption; try lia. simpl. lia. }
              { assumption. }
Qed.

Theorem insertTTree : forall x t,
  isTTtree t ->
  isTTtree (insert x t).
Proof.
  intros x t H.
  inversion H. constructor.
  - apply orderedInsert. assumption.
  - apply balancedInsert. assumption.
Qed.

(* =================== Invariant maintenance for deletion =================== *)

Theorem deleteOrderedTTree : forall x t,
  ordered t ->
  ordered (delete x t).
Proof.
Admitted.

Theorem deleteBalancedTTree : forall x t,
  balanced t ->
  balanced (delete x t).
Proof.
Admitted.

Theorem deleteTTree : forall x t,
  isTTtree t ->
  isTTtree (delete x t).
Proof.
Admitted.

(* =================== Lookup + insertion algebraic proofs =================== *)


Theorem lookupEmpty : forall x : nat, lookup x Empty = false.
Proof.
  intros x.
  simpl.
  reflexivity.
Qed.

Theorem lookupInsert : forall (x : nat) (tree : TTtree),
  lookup x (insert x tree) = true.
Proof.
  intros x tree.
  unfold insert.
  destruct (lookup x tree) eqn:Hlookup.
  - (* lookup x tree = true *)
    simpl. assumption.
  - (* lookup x tree = false *)
    generalize dependent tree.
    induction tree as [| l IHl v r IHr | l IHl v1 m IHm v2 r IHr]; intros.
    + (* Case: tree = Empty *)
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* Case: tree = Node2 l v r *)
      simpl.
      unfold convertRootKickUp.
      bdestruct (x <? v).
      * (* x < v *)
        destruct (upward x l) eqn:Hup.
        -- (* upward x l = Normal t *)
           simpl in *. rewrite IHl.
           ++ bdall.
           ++ revert Hlookup. bdall.
        -- (* upward x l = KickUp l0 v0 r0 *)
           simpl in *.
           bdestruct (x=?v0) as Hvalue.
           ++ simpl. reflexivity.
           ++ bdestruct (x <? v); try lia. bdall.
      * (* x >= v *)
        destruct (upward x r) eqn:Hup.
        -- (* upward x r = Normal t *)
           simpl in *. rewrite IHr.
           ++ bdall.
           ++ revert Hlookup. bdall.
        -- (* upward x r = KickUp l0 v0 r0 *)
           simpl in *.
           bdall.
           bdestruct (x<?v0) as Hvalue.
           ++ lia.
           ++ apply IHr. apply Hlookup.
           ++ bdestruct (x<?v0).
              ** apply IHr. apply Hlookup.
              ** lia.
    + (* Case: tree = Node3 l v1 m v2 r *)
      simpl in *.
      unfold convertRootKickUp.
      bdestruct (x <? v1).
      * (* x < v1 *)
        destruct (upward x l) eqn:Hup.
        -- (* upward x l = Normal t *)
           simpl in *. rewrite IHl.
           bdestruct (x=?v2).
           ++ bdall.
           ++ bdall.
           ++ revert Hlookup. bdall.
        -- (* upward x l = KickUp l0 v0 r0 *)
           simpl in *.
           bdall.
           simpl in Hlookup.
           ++ discriminate Hlookup.
           ++ simpl in Hlookup. discriminate Hlookup.
      * (* Subcase: x >= v1 *)
        -- bdestruct (v2 <? x).
           ++ (* x > v2 *)
              destruct (upward x r) eqn:Hup.
              ** (* upward x r = Normal t *)
                 simpl in *. rewrite IHr.
                 --- bdall.
                 --- bdestruct (x=?v1).
                     { simpl in Hlookup. discriminate Hlookup. }
                     { bdestruct (x=?v2).
                       - simpl in Hlookup. discriminate Hlookup.
                       - simpl in Hlookup. apply Hlookup. }
              ** (* upward x r = KickUp l0 v r0 *)
                 simpl in *. rewrite IHr.
                 --- bdall.
                 --- bdestruct (x=?v1).
                     { simpl in Hlookup. discriminate Hlookup. }
                     { bdestruct (x=?v2).
                       - simpl in Hlookup. discriminate Hlookup.
                       - simpl in Hlookup. apply Hlookup. }
           ++ (* v1 <= x <= v2 *)
              destruct (upward x m) eqn:Hup.
              ** (* upward x m = Normal t *)
                 simpl in *. rewrite IHm.
                 --- bdall.
                 --- bdestruct (x=?v1).
                     { simpl in Hlookup. discriminate Hlookup. }
                     { bdestruct (x=?v2).
                       - simpl in Hlookup. discriminate Hlookup.
                       - simpl in Hlookup. apply Hlookup. }
              ** (* upward x m = KickUp l0 v r0 *)
                 simpl in *.
                 bdestruct (x=?v).
                 --- reflexivity.
                 --- bdall.
                     { simpl in Hlookup. discriminate Hlookup. }
                     { simpl in Hlookup. discriminate Hlookup. }
Qed.

Theorem lookupInsertNeq : forall (t : TTtree) (v v' : nat),
  ordered t ->
  v <> v' ->
  lookup v' (insert v t) = lookup v' t.
Proof.
  intros t v v' Hordered Hneq.
  unfold insert.
  destruct (lookup v t) eqn:Hlookup.
  - (* lookup v t = true *)
    reflexivity.
  - (* lookup v t = false *)
    induction t as [| l IHl value r IHr | l IHl value1 m IHm value2 r IHr]; intros.
    + (* Case: t = Empty *)
      simpl.
      bdestruct (v' =? v).
      * lia.
      * bdall.
    + (* Case: t = Node2 l value r *)
      simpl.
      unfold convertRootKickUp.
      bdestruct (v<?value).
      * (* v < value *)
        destruct (upward v l) eqn:Hup.
        ++ (* upward v l = Normal t *)
           simpl in *.
           bdestruct (v'=?value).
           ** reflexivity.
           ** bdestruct (v'<?value).
              --- apply IHl.
                  { inversion Hordered. assumption. }
                  { revert Hlookup. bdall. }
              --- reflexivity.
        ++ (* upward v l = KickUp l0 v0 r0 *)
           bdestruct (v'=?value).
           ** simpl. bdall.
           ** simpl in *. bdestruct (v' =? v0).
              --- simpl. revert Hlookup. bdall.
                  { apply IHl. inversion Hordered. assumption. }
                  { inversion Hordered. apply ForallTTtreeUpward with (v:=v) in H7.
                    rewrite Hup in H7. simpl in H7. destruct H7.
                    - lia.
                    - assumption. }
              --- simpl. revert Hlookup. bdall.
                  { apply IHl. inversion Hordered. assumption. }
                  { inversion Hordered. apply ForallTTtreeUpward with (v:=v) in H10.
                    rewrite Hup in H10. simpl in H10. destruct H10.
                    - lia.
                    - assumption. }
                  { apply IHl. inversion Hordered. assumption. }
      * (* v >= value *)
        destruct (upward v r) eqn:Hup.
        ++ (* upward v r = Normal t *)
           simpl in *.
           bdestruct (v'=?value).
           ** reflexivity.
           ** bdestruct (v'<?value).
              --- reflexivity.
              --- apply IHr.
                  { inversion Hordered. assumption. }
                  { revert Hlookup. bdall. }
        ++ (* upward v r = KickUp l0 v0 r0 *)
           bdestruct (v'=?value).
           ** simpl. bdall.
           ** simpl in *. bdestruct (v' =? v0).
              --- simpl. revert Hlookup. bdall. simpl.
                  { inversion Hordered. apply ForallTTtreeUpward with (v:=v) in H9.
                    rewrite Hup in H9. simpl in H9. destruct H9.
                    - lia.
                    - lia. }
                  { apply IHr. inversion Hordered. assumption. }
              --- simpl. revert Hlookup. bdall.
                  { simpl. bdestruct (v' <? v0).
                    - lia.
                    - apply IHr. inversion Hordered. assumption. }
                  { simpl. bdestruct (v' <? v0).
                    - apply IHr. inversion Hordered. assumption.
                    - lia. }
    + (* Case: tree = Node3 l v1 m v2 r *)
      simpl in *.
      bdestruct (v <? value1).
      * (* v < value1 *)
        destruct (upward v l) eqn:Hup.
        ++ (* upward v l = Normal t *)
           simpl.
           bdestruct (v' =? value1).
           ** simpl. reflexivity.
           ** bdestruct (v' =? value2).
              --- simpl. reflexivity.
              --- simpl in *. bdall. apply IHl.
                  { inversion Hordered. assumption. }
                  { revert Hlookup. bdall. }
        ++ (* upward v l = KickUp l0 v0 r0 *)
           simpl.
           bdestruct (v' =? value1).
           simpl in *.
           ** reflexivity.
           ** bdestruct (v' =? value2).
              --- bdestruct (v' <? value1). simpl in IHl.
                  { bdall.
                    - destruct (lookup value2 l).
                      ++ apply IHl.
                         * inversion Hordered. assumption.
                         * revert Hlookup. bdall.
                      ++ inversion Hordered. apply ForallTTtreeUpward with (v:=v) in H10.
                         * rewrite Hup in H10. simpl in H10. destruct H10. lia.
                         * lia.
                    - inversion Hordered. apply ForallTTtreeUpward with (v:=v) in H10.
                      rewrite Hup in H10. simpl in H10. destruct H10. lia. lia. }
                  { simpl. reflexivity. }
              --- bdestruct (v' <? value1). simpl in IHl.
                  { bdall.
                    - apply IHl.
                      ++ inversion Hordered. assumption.
                      ++ revert Hlookup. bdall.
                    - apply IHl.
                      ++ inversion Hordered. assumption.
                      ++ revert Hlookup. bdall.
                    - apply IHl.
                      ++ inversion Hordered. assumption.
                      ++ revert Hlookup. bdall. }
                  { bdall. }
      * (* v >= value1 *)
        unfold convertRootKickUp.
        bdestruct (value2 <? v).
        ++ (* v > value2 *)
           destruct (upward v r) eqn:Hup.
           ** (* upward v r = Normal t *)
              simpl.
              bdestruct (v' =? value1).
              --- simpl. reflexivity.
              --- bdestruct (v' =? value2).
                  { simpl. reflexivity. }
                  { simpl in *. bdall. apply IHr.
                    - inversion Hordered. assumption.
                    - bdestruct (v =? value1).
                      ++ simpl in Hlookup. discriminate Hlookup.
                      ++ bdestruct (v =? value2).
                         * simpl in Hlookup. discriminate Hlookup.
                         * simpl in Hlookup. apply Hlookup. }
           ** (* upward v r = KickUp l0 v0 r0 *)
              simpl.
              bdestruct (v' =? value2).
              -- bdall.
              -- bdestruct (v' <? value2).
                 --- bdestruct (v' =? value1). simpl in *.
                     { reflexivity. }
                     { bdall. }
                 ---  simpl in *. bdestruct (v' =? v0).
                     { bdestruct (v' =? value1).
                       - simpl. reflexivity.
                       - simpl. bdall.
                         ++ inversion Hordered.
                            apply ForallTTtreeUpward with (v:=v) in H13.
                            rewrite Hup in H13. simpl in H13. destruct H13.
                            * lia.
                            * lia.
                         ++ apply IHr.
                            * inversion Hordered. assumption.
                            * revert Hlookup. bdall. simpl. discriminate 1. }
                     { simpl in *. bdestruct (v' <? v0).
                       - bdestruct (v' =? value1).
                         ++ simpl. inversion Hordered. lia.
                         ++ simpl. bdestruct (v' <? value1).
                            * inversion Hordered. lia.
                            * bdestruct (value2 <? v').
                              apply IHr. inversion Hordered. assumption.
                              bdestruct (v =? value1). bdestruct (v =? value2).
                              -- simpl in Hlookup. discriminate Hlookup.
                              -- simpl in Hlookup. discriminate Hlookup.
                              -- revert Hlookup. bdall.
                              -- lia.
                       - bdestruct (v' =? value1).
                         ++ simpl. inversion Hordered. lia.
                         ++ simpl. bdall.
                            * inversion Hordered. lia.
                            * apply IHr. inversion Hordered. assumption. revert Hlookup. bdall. simpl. discriminate 1. }
        ++ (* value1 <= v <= value2 *)
           destruct (upward v m) eqn:Hup.
           ** (* upward v m = Normal t *)
              simpl.
              bdestruct (v' =? value1).
              --- simpl. reflexivity.
              --- bdestruct (v' =? value2).
                 { simpl. reflexivity. }
                 { simpl in *. bdall. apply IHm. inversion Hordered. assumption. bdestruct (v =? value1).
                   - simpl. simpl in Hlookup. discriminate Hlookup.
                   - revert Hlookup. bdall. }
           ** (* upward v m = KickUp l0 v0 r0 *)
              simpl in *.
              bdestruct (v' =? value1).
              --- bdall. inversion Hordered. apply ForallTTtreeSplit in H12. destruct H12.
                 apply ForallTTtreeUpward with (v:=v) in H12. rewrite Hup in H12. simpl in H12.
                 { destruct H12. destruct H18. apply ForallTTtreeUpward with (v:=v) in H19. lia. lia. }
                 { lia. }
              --- bdestruct (v' =? v0).
                  { bdestruct (v' =? value2).
                    - simpl. reflexivity.
                    - simpl. bdestruct (v' <? value1).
                      ++ inversion Hordered. apply ForallTTtreeSplit in H12. destruct H12.
                         apply ForallTTtreeUpward with (v:=v) in H12. rewrite Hup in H12. simpl in H12.
                         destruct H12. lia. bdestruct (v =? value1).
                         * simpl in Hlookup. discriminate Hlookup.
                         * lia.
                      ++ bdestruct (value2 <? v').
                         * inversion Hordered.
                           apply ForallTTtreeSplit in H13. destruct H13.
                           apply ForallTTtreeUpward with (v:=v) in H18.
                           rewrite Hup in H18. simpl in H18. destruct H18. lia.
                           bdestruct (v =? value2). revert Hlookup. bdall. simpl. discriminate 1. lia.
                         * apply IHm. inversion Hordered. assumption. bdestruct (v =? value1).
                           -- simpl in Hlookup. discriminate Hlookup.
                           -- bdestruct (v =? value1).
                              ** inversion Hordered. lia.
                              ** bdestruct (v =? value2). simpl in Hlookup. discriminate Hlookup.
                                 simpl in Hlookup. apply Hlookup. }
                  { bdestruct (v' <? v0).
                    - bdestruct (v' <? value1).
                      ++ bdestruct (v' =? value2).
                         * inversion Hordered. lia.
                         * simpl. reflexivity.
                      ++ bdestruct (v' =? value2).
                         * simpl. inversion Hordered. apply ForallTTtreeSplit in H13.
                           destruct H13. apply ForallTTtreeUpward with (v:=v) in H18.
                           rewrite Hup in H18. simpl in H18.
                           destruct H18. lia. lia.
                         * simpl. bdestruct (value2 <? v').
                           -- inversion Hordered. apply ForallTTtreeSplit in H14.
                              destruct H14. apply ForallTTtreeUpward with (v:=v) in H19.
                              rewrite Hup in H19. simpl in H19. destruct H19. lia.
                              bdestruct (v =? value2).
                              ** revert Hlookup. bdall. simpl. discriminate 1.
                              ** lia.
                           -- apply IHm. inversion Hordered. assumption. bdestruct (v =? value1).
                              simpl in Hlookup. discriminate Hlookup. revert Hlookup. bdall.
                    - bdestruct (v' =? value2).
                      ++ simpl. reflexivity.
                      ++ bdestruct (v' <? value2).
                         * simpl. bdestruct (v' <? value1).
                           -- inversion Hordered. apply ForallTTtreeSplit in H14.
                              destruct H14. apply ForallTTtreeUpward with (v:=v) in H14.
                              rewrite Hup in H14. simpl in H14. lia. bdestruct (v =? value1).
                              simpl in Hlookup. discriminate Hlookup. lia.
                           -- bdestruct (value2 <? v').
                              ** inversion Hordered. apply ForallTTtreeSplit in H15.
                                 destruct H15. apply ForallTTtreeUpward with (v:=v) in H15.
                                 rewrite Hup in H15. simpl in H15. lia. bdestruct (v =? value1).
                                 simpl in Hlookup. discriminate Hlookup. lia.
                              ** apply IHm. inversion Hordered. assumption. bdestruct (v =? value1).
                                 simpl in Hlookup. discriminate Hlookup. revert Hlookup. bdall.
                         * simpl. bdestruct (v' <? value1).
                           -- inversion Hordered. apply ForallTTtreeSplit in H14.
                              destruct H14. apply ForallTTtreeUpward with (v:=v) in H14.
                              rewrite Hup in H14. simpl in H14. lia. bdestruct (v =? value1).
                              simpl in Hlookup. discriminate Hlookup. lia.
                           -- bdestruct (value2 <? v').
                              ** reflexivity.
                              ** inversion Hordered. apply ForallTTtreeSplit in H15.
                                 destruct H15. apply ForallTTtreeUpward with (v:=v) in H20.
                                 rewrite Hup in H20. simpl in H20. lia. bdestruct (v =? value1).
                                 simpl in Hlookup. discriminate Hlookup. lia. }
Qed.

Theorem commutativity_insert : forall x y z tree,
  ordered tree ->
  lookup z (insert x (insert y tree)) = lookup z (insert y (insert x tree)).
Proof.
  intros x y z tree Hordered.
  bdestruct (x=?y).
  - (* x = y *)
    subst.
    reflexivity.
  - (* x <> y *)
    bdestruct (z=?x).
    + (* z = x *)
      subst.
      rewrite lookupInsert. rewrite lookupInsertNeq.
      * rewrite lookupInsert. reflexivity.
      * apply orderedInsert. assumption.
      * lia.
    + (* z <> x *)
      bdestruct (z=?y).
      * (* z = y *)
        subst.
        rewrite lookupInsert. rewrite lookupInsertNeq.
        -- rewrite lookupInsert. reflexivity.
        -- apply orderedInsert. assumption.
        -- lia.
      * (* z <> y *)
        destruct (lookup y tree) eqn:Hlookup_y.
        { (* lookup y tree = true *)
          repeat rewrite lookupInsertNeq; try assumption; try reflexivity; try lia.
          -- apply orderedInsert. assumption.
          -- apply orderedInsert. assumption. }
        { (* lookup y tree = false *)
          destruct (lookup x tree) eqn:Hlookup_x.
          { (* lookup x tree = true *)
            repeat rewrite lookupInsertNeq; try assumption; try reflexivity; try lia.
            -- apply orderedInsert. assumption.
            -- apply orderedInsert. assumption. }
          { (* lookup x tree = false *)
            repeat rewrite lookupInsertNeq; try assumption; try reflexivity; try lia.
            -- apply orderedInsert. assumption.
            -- apply orderedInsert. assumption. } }
Qed.

(* =================== Lookup + deletion algebraic proofs =================== *)

Theorem lookupDelete : forall (x : nat) (tree : TTtree),
  lookup x (delete x tree) = false.
Proof.
Admitted.

Theorem lookupDeleteNeq : forall (t : TTtree) (v v' : nat),
  ordered t ->
  v <> v' ->
  lookup v' (delete v t) = lookup v' t.
Proof.
Admitted.

Theorem commutativityDelete : forall x y z tree,
  ordered tree ->
  lookup z (delete x (delete y tree)) = lookup z (delete y (delete x tree)).
Proof.
Admitted.



