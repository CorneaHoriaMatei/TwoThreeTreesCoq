Require Import Nat.
Require Import Bool.
Require Import List.
Import ListNotations.

(* =================== 2-3 Tree data type =================== *)
Inductive TTtree : Type :=
  | Empty (* Empty Tree *)
  | Node2 (l : TTtree) (v : nat) (r : TTtree) (* 2-Node *)
  | Node3 (l : TTtree) (v1 : nat) (m : TTtree) (v2 : nat) (r : TTtree) (* 3-Node *)
.

(* =================== 2-3 Tree examples =================== *)
Definition exampleTree1 : TTtree :=
  Node3 
    (Node2 Empty 1 Empty)
    2
    (Node2 Empty 3 Empty)
    4
    (Node2 Empty 7 Empty).


Definition exampleTree2 : TTtree :=
  Node2
    (Node3 (Node2 Empty 2 Empty) 4 (Node2 Empty 5 Empty) 6 (Node2 Empty 7 Empty))
    8
    (Node2 (Node3 Empty 9 Empty 12 Empty) 15 (Node2 Empty 17 Empty)).


(* =================== Function that converts a 2-3 Tree to a list =================== *)

Fixpoint convertToList (t : TTtree) : list nat :=
  match t with
  | Empty => []
  | Node2 l v r => convertToList l ++ [v] ++ (convertToList r)
  | Node3 l v1 m v2 r => convertToList l ++ [v1] ++ convertToList m ++ [v2] ++ convertToList r
  end
.

(* Some short tests for convertToList *)
Compute (convertToList exampleTree1).

Compute (convertToList exampleTree2).

(* =================== Lookup operation =================== *)
Fixpoint lookup (x : nat) (t : TTtree) : bool :=
  match t with
  | Empty => false
  | Node2 l v r =>
      if x =? v then true
      else if x <? v then lookup x l
      else lookup x r
  | Node3 l v1 m v2 r =>
      if (x =? v1) || (x =? v2) then true
      else if x <? v1 then lookup x l
      else if v2 <? x then lookup x r
      else lookup x m
  end
.

(* Some short tests for lookup *)
Compute (lookup 3 exampleTree1).

Compute (lookup 5 exampleTree1).

Compute (lookup 3 exampleTree2).

Compute (lookup 5 exampleTree2).

(* =================== Insertion =================== *)
Inductive InsertionTTtree : Type :=
  | Normal (t: TTtree)
  | KickUp (l : TTtree) (v: nat) (r : TTtree)
.

Fixpoint upward (x : nat) (t : TTtree) : InsertionTTtree :=
  match t with
  | Empty => KickUp Empty x Empty
  | Node2 l v r =>
      if x <? v then (* When the KickUp is coming from the left child *)
        match upward x l with
        | Normal t' => Normal (Node2 t' v r)
        | KickUp l' v' r' => Normal (Node3 l' v' r' v r)
        end
      else (* When the KickUp is coming from the right child *)
        match upward x r with
        | Normal t' => Normal (Node2 l v t')
        | KickUp l' v' r' => Normal (Node3 l v l' v' r')
        end
  | Node3 l v1 m v2 r =>
      if x <? v1 then (* When the KickUp is coming from the left child *)
        match upward x l with
        | Normal t' => Normal (Node3 t' v1 m v2 r)
        | KickUp l' v' r' => KickUp (Node2 l' v' r') v1 (Node2 m v2 r)
        end
      else if v2 <? x then (* When the KickUp is coming from the right child *)
        match upward x r with
        | Normal t' => Normal (Node3 l v1 m v2 t')
        | KickUp l' v' r' => KickUp (Node2 l v1 m) v2 (Node2 l' v' r')
        end
      else (* When the KickUp is coming from the middle child *)
        match upward x m with
        | Normal t' => Normal (Node3 l v1 t' v2 r)
        | KickUp l' v' r' => KickUp (Node2 l v1 l') v' (Node2 r' v2 r)
        end
  end
.

Definition convertRootKickUp (tempTTtree : InsertionTTtree) : TTtree :=
  match tempTTtree with
  | Normal t => t
  | KickUp l v r => Node2 l v r
  end
.

(* Insert function *)
Definition insert (x : nat) (t : TTtree) : TTtree :=
  match lookup x t with
  | true => t (* If the element is already in the tree *)
  | false => convertRootKickUp (upward x t) (* If not, we insert it in the tree *)
  end
.

(* Some short tests for insertion *)
Compute (convertToList exampleTree1).

Compute (convertToList exampleTree2).

Compute (convertToList (insert 2 exampleTree1)).

Compute (convertToList (insert 9 exampleTree2)).

Compute (convertToList (insert 5 exampleTree1)).

Compute (convertToList (insert 1 exampleTree2)).

Compute (convertToList (insert 10 exampleTree1)).

Compute (convertToList (insert 14 exampleTree2)).

(* =================== Deletion =================== *)

Inductive DeletionTTtree : Type :=
  | NormalTree (t : TTtree)
  | Hole (t : TTtree)
.

Definition node2Left (hole : TTtree) (root : nat) (right : TTtree) : DeletionTTtree :=
  match right with
  | Empty => Hole Empty
  | Node2 l v r => Hole (Node3 hole root l v r)
  | Node3 l v1 m v2 r => NormalTree (Node2 (Node2 hole root l) v1 (Node2 m v2 r))
  end
.

Definition node2Right (left : TTtree) (root : nat) (hole : TTtree) : DeletionTTtree :=
  match left with
  | Empty => Hole Empty
  | Node2 l v r => Hole (Node3 l v r root hole)
  | Node3 l v1 m v2 r => NormalTree (Node2 (Node2 l v1 m) v2 (Node2 r root hole))
  end
.

Definition node3Left (hole : TTtree) (leftValue : nat) (mid : TTtree) (rightValue : nat) (right : TTtree) : DeletionTTtree :=
  match mid with
  | Empty => Hole Empty
  | Node2 l v r => NormalTree (Node2 (Node3 hole leftValue l v r) rightValue right)
  | Node3 l v1 m v2 r => NormalTree (Node3 (Node2 hole leftValue l) v1 (Node2 mid v2 r) rightValue right)
  end
.

Definition node3Mid (left : TTtree) (leftValue : nat) (hole : TTtree) (rightValue : nat )(right : TTtree) : DeletionTTtree :=
  match right with
  | Empty => Hole Empty
  | Node2 l v r => NormalTree (Node2 left leftValue (Node3 hole rightValue l v r))
  | Node3 l v1 m v2 r => NormalTree (Node3 left leftValue (Node2 hole rightValue l) v1 (Node2 m v2 r))
  end
.

Definition node3Right (left : TTtree) (leftValue : nat) (mid : TTtree) (rightValue : nat) (hole : TTtree) : DeletionTTtree :=
  match mid with
  | Empty => Hole Empty
  | Node2 l v r => NormalTree (Node2 left leftValue (Node3 l v r rightValue hole))
  | Node3 l v1 m v2 r => NormalTree (Node3 left leftValue (Node2 l v1 m) v2 (Node2 r rightValue hole))
  end
.

Definition emptyTree (t : TTtree) : bool :=
  match t with
  | Empty => true
  | _ => false
  end
.

Fixpoint upwardDelete (x : nat) (t : TTtree) : DeletionTTtree :=
  match t with
  | Empty => Hole Empty (* Cannot be the case *)
  | Node2 l v r =>
    match emptyTree l with
    | true => Hole Empty (* In case there is a terminal 2-Node*)
    | false => (* Look at where the hole is coming from with a 2-Node parent*)
        if x <? v then
          match upwardDelete x l with
          | NormalTree n => NormalTree (Node2 n v r)
          | Hole h => node2Left h v r
          end
        else (* if v <? x then *)
          match upwardDelete x r with
          | NormalTree n => NormalTree (Node2 l v n)
          | Hole h => node2Right l v h
          end
    end
  | Node3 l v1 m v2 r =>
    match emptyTree l with
    | true => (* In case it is a terminal 3-Node *)
        if x =? v1 then NormalTree (Node2 Empty v2 Empty)
        else NormalTree (Node2 Empty v1 Empty)
    | false => (* Look at where the whole is coming from with a 3-Node parent *)
        if x <? v1 then
          match upwardDelete x l with
          | NormalTree n => NormalTree (Node3 n v1 m v2 r)
          | Hole h => node3Left h v1 m v2 r
          end
        else if v2 <? x then
          match upwardDelete x r with
          | NormalTree n => NormalTree (Node3 l v1 m v2 n)
          | Hole h => node3Right l v1 m v2 h
          end
        else
          match upwardDelete x m with
          | NormalTree n => NormalTree (Node3 l v1 n v2 r)
          | Hole h => node3Mid l v1 h v2 r
          end
    end
  end
.

Definition convertRootHole (t : DeletionTTtree) : TTtree :=
  match t with
  | NormalTree tree => tree
  | Hole tree => tree
  end
.

Fixpoint leaf (x : nat) (t : TTtree) : bool :=
  match t with
  | Empty => false (* Cannot be the case *)
  | Node2 l v r => 
      if x <? v then leaf x l
      else if v <? x then leaf x r
      else emptyTree l
  | Node3 l v1 m v2 r => 
      if x =? v1 then emptyTree l
      else if x =? v2 then emptyTree l
      else if x <? v1 then leaf x l
      else if v2 <? x then leaf x r
      else leaf x m
  end
.

Fixpoint retrieveSuccessor (t : TTtree) : nat :=
  match t with
  | Empty => 0 (* Cannot be the case *)
  | Node2 l v r =>
      match l with
      | Empty => v
      | Node2 l' v' r' => retrieveSuccessor l'
      | Node3 l' v1' m' v2' r' => retrieveSuccessor l'
      end
  | Node3 l v1 m v2 r =>
    match l with
    | Empty => v1
    | Node2 l' v' r' => retrieveSuccessor l'
    | Node3 l' v1' m' v2' r' => retrieveSuccessor l'
    end
  end
.

Fixpoint successor (x : nat) (t : TTtree) : nat :=
  match t with
  | Empty => 0 (* Cannot be the case *)
  | Node2 l v r => 
      if x =? v then retrieveSuccessor r
      else if x <? v then successor x l
      else successor x r
  | Node3 l v1 m v2 r =>
      if x =? v1 then retrieveSuccessor m
      else if x =? v2 then retrieveSuccessor r
      else if x <? v1 then successor x l
      else if v2 <? x then successor x r
      else successor x m
  end
.

Fixpoint replace (x y : nat) (t : TTtree) : TTtree :=
  match t with
  | Empty => Empty (* Cannot be the case *)
  | Node2 l v r =>
      if v =? x then Node2 l y r
      else if x <? v then Node2 (replace x y l) v r
      else Node2 l v (replace x y r)
  | Node3 l v1 m v2 r =>
      if x =? v1 then Node3 l y m v2 r
      else if x =? v2 then Node3 l v1 m y r
      else if x <? v1 then Node3 (replace x y l) v1 m v2 r
      else if v2 <? x then Node3 l v1 m v2 (replace x y r)
      else Node3 l v1 (replace x y m) v2 r
  end
.

(* Delete function *)
Definition delete (x : nat) (t : TTtree) : TTtree :=
  match lookup x t with
  | false => t (* If the value is not in the tree, then we have nothing to delete *)
  | true => 
      match leaf x t with (* Based on whether the value we want to delete is in a terminal node or not, we have 2 cases *)
      | true => convertRootHole (upwardDelete x t)
      | false => let y := successor x t in replace x y (convertRootHole (upwardDelete y t))
      end
  end
.


(* Some short tests for deletion *)
Compute (convertToList exampleTree1).

Compute (convertToList exampleTree2).

(* Deleting values that do not exist *)
Compute (convertToList (delete 5 exampleTree1)).

Compute (convertToList (delete 3 exampleTree2)).

(* Deleting values from terminal nodes *)
Compute (convertToList (delete 1 exampleTree1)).

Compute (convertToList (delete 7 exampleTree2)).

Compute (convertToList (delete 12 exampleTree2)).

Compute (convertToList (delete 17 exampleTree2)).

(* Deleting values from non-terminal nodes*)
Compute (convertToList (delete 2 exampleTree1)).

Compute (convertToList (delete 4 exampleTree2)).

Compute (convertToList (delete 6 exampleTree2)).

Compute (convertToList (delete 15 exampleTree2)).


