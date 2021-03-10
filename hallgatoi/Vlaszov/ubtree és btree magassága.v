Inductive UBtree : Set :=
  | leaf0 : UBtree
  | node2 : UBtree -> UBtree -> UBtree
  | node1 : UBtree -> UBtree.

Fixpoint right_UB (t:UBtree) (s:UBtree) : UBtree :=
  match t with
    | leaf0 => node2 leaf0 s
    | node1 t0 => node1 (right_UB t0 s)
    | node2 tl tr => node2 tl (right_UB tr s) end.

Fixpoint length_UB (t : UBtree) : nat :=
  match t with
    | leaf0 => 1
    | node1 t3 => (length_UB t3)
    | node2 t4 t5 => (length_UB t4) + (length_UB t5) end.

Theorem osszhossz: forall s t : UBtree, length_UB(right_UB s t) =  length_UB s + length_UB t.
Proof.
  intros.
  induction s; simpl; auto.
  rewrite IHs2.
  Require Import Omega.
  omega.
  Show Proof.
Qed.

Inductive bTree : Set :=
  | bleaf : bool -> bTree
  | bnode : (bool -> bool -> bool) -> bTree -> bTree -> bTree.

Print max.

Fixpoint b_height (t : bTree) : nat :=
  match t with
  | bleaf true => 1
  | bleaf false => 1
  | bnode op bt1 bt2 => 1 + (max (b_height bt1) (b_height bt2)) end.

Eval compute in b_height (bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true))).

  

  