Inductive UBTree : Set :=
  | leaf0 : UBTree
  | node2 : UBTree -> UBTree -> UBTree
  | node1 : UBTree -> UBTree.

Fixpoint right_UB (t:UBTree) (s:UBTree) : UBTree :=
  match t with
    | leaf0 => node2 leaf0 s
    | node2 t0 t1 => node2 t0 (right_UB t1 s)
    | node1 t => node1 (right_UB t s)
  end. 

Eval compute in right_UB (node2 leaf0 leaf0) (node2 leaf0 (node2 leaf0 leaf0)).
Eval compute in right_UB (node2 leaf0 (node1 leaf0)) (node2 leaf0 (node2 leaf0 leaf0)).

Fixpoint length_UB (t:UBTree) : nat :=
  match t with
    | leaf0 => 1
    | node2 t1 t2 => (length_UB t1) + (length_UB t2)
    | node1 t => length_UB t
  end.

Eval compute in length_UB (right_UB (node2 leaf0 leaf0) (node2 leaf0 (node2 leaf0 leaf0))).
Eval compute in length_UB (right_UB (node2 leaf0 (node1 leaf0)) (node2 leaf0 (node2 leaf0 leaf0))).

Theorem right_UB_length : forall s t:UBTree, length_UB(right_UB s t) = length_UB s + length_UB t.
Proof.
  induction s, t.
  simpl; reflexivity.
  simpl; reflexivity.
  simpl; reflexivity.
  Require Import Omega.
  simpl. rewrite IHs2. simpl. omega.
  simpl. rewrite IHs2. simpl. omega.
  simpl. rewrite IHs2. simpl. omega.
  simpl. rewrite IHs. simpl. reflexivity.
  simpl. rewrite IHs. simpl. reflexivity.
  simpl. rewrite IHs. simpl. reflexivity.
Qed.
