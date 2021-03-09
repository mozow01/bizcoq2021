Inductive UBTree : Set :=
  | leaf0 : UBTree
  | node2 : UBTree -> UBTree -> UBTree
  | node1 : UBTree -> UBTree.

Fixpoint right_UB (t s : UBTree) : UBTree :=
  match t with
    | leaf0 => node2 leaf0 s
    | node2 t0 t1 => node2 t0 (right_UB t1 s)
    | node1 t3 => node1 (right_UB t3 s)end.

Fixpoint length_UB (t:UBTree) : nat :=
  match t with
    | leaf0 => 1
    | node2 t1 t2 => (length_UB t1) + (length_UB t2)
    | node1 t3 =>(length_UB t3) end.

Theorem UBThreeoem :forall s t : UBTree, length_UB(right_UB s t) =  length_UB s + length_UB t.
Proof.
  intros.
  induction s.
  simpl.
  reflexivity.
  simpl.
  rewrite IHs2.
  Require Import Omega.
  omega.
  simpl.
  rewrite IHs.
  reflexivity.
Qed.

Inductive bTree : Set :=
  | bleaf : bool -> bTree
  | bnode : (bool -> bool -> bool) -> bTree -> bTree -> bTree.

Eval compute in max 1 0.

Fixpoint length_b (t:bTree) : nat :=
  match t with
    | bleaf b0 => 0
    | bnode muv1 b1 b2=> 1 + max(length_b b1) (length_b b2) end.

Search bool.

Eval compute in length_b (bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true))).

Fixpoint tukorkep (t:bTree) : bTree :=
  match t with
    | bleaf b0 => bleaf b0
    | bnode muv1 b1 b2 => bnode muv1 (tukorkep b2) (tukorkep b1) end.

Eval compute in tukorkep (bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true))).

Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

(* pl.: *)

Check hleaf true.
Check hnode 0 andb (hleaf true) (hleaf true).


Fixpoint forgetful (n:nat) (t: hbTree n) : bTree := 
  match t with
    | hleaf b0 => bleaf b0 
    | hnode n0 muv t1 t2 => bnode muv (forgetful n0 t1) (forgetful n0 t2) end.

Eval simpl in forgetful 1 (hnode 0 andb (hleaf true) (hleaf true)).


Fixpoint height (t:bTree) : nat :=
  match t with
    | bleaf b0 => 0
    | bnode muv1 b1 b2 => 1 + max(height b1) (height b2) end.




Theorem magassagtetel : forall (n:nat) (t: hbTree n), height(forgetful n t) = n. 
Proof.
  intros.
  induction t.
  unfold forgetful.
  unfold height.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  Search max.
  rewrite Nat.max_id.
  reflexivity.
Qed.






 
 

