(* a *)

Inductive UBTree : Set :=
| leaf0 : UBTree
| node1 : UBTree -> UBTree
| node2 : UBTree -> UBTree -> UBTree.

Check node1 (node2 leaf0 (node1 leaf0)) : UBTree.

(* b *)

Fixpoint right_UB (t: UBTree) (s: UBTree) : UBTree :=
match t with
| leaf0 => node2 leaf0 s
| node1 p => node1 (right_UB p s)
| node2 x y => node2 x (right_UB y s)
end.

Check node1 (node2 leaf0 (node1 leaf0)) : UBTree.
Eval compute in right_UB (node1 leaf0) (node2 (node1 leaf0) leaf0).
Eval compute in right_UB (leaf0) (node2 (node1 leaf0) leaf0).

(* c *)

Fixpoint length_UB (t: UBTree) : nat :=
match t with
| leaf0 => 1
| node1 p => length_UB(p) + 1
| node2 x y => length_UB(x) + length_UB(y)
end.

Eval compute in length_UB (node2 (node1 leaf0) leaf0).
Eval compute in length_UB (node2 (node1 (node2 leaf0 leaf0)) leaf0).

Require Import Arith.
Require Import Omega.

Theorem length_right : forall s t : UBTree, length_UB(right_UB s t) =  length_UB s + length_UB t.
Proof.
  intros.
  induction s, t.
  auto.
  auto.
  auto.
  simpl.
  auto.
  simpl in IHs.
  simpl.
  rewrite Nat.add_assoc.
  rewrite Nat.add_assoc in IHs.
  apply f_equal2_plus.
  omega.
  reflexivity.
  simpl.
  simpl in IHs.
  rewrite Nat.add_assoc.
  rewrite Nat.add_assoc in IHs.
  omega.
  simpl; simpl in IHs2.
  omega.
  simpl; simpl in IHs2.
  omega.
  simpl; simpl in IHs2.
  omega.
Defined.

