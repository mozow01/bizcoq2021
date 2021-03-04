Theorem n_plus_O : forall n : nat, n + O = n.
Proof.
  induction n.
  simpl.
  congruence.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
Require Import Omega.
  induction n, m; omega.
Qed.


Inductive tree : Set :=
  | l : tree
  | n : tree -> tree -> tree.

Check n l (n l l).

Fixpoint length (t:tree) : nat :=
  match t with
    | l => 1
    | n t1 t2 => (length t1) + (length t2) end.

Eval compute in length(l).

Definition levelhossz : length(l)=1.
unfold length.
reflexivity.
Defined.

Fixpoint right (t s : tree) : tree :=
  match t with
    | l => n l s
    | n t0 t1 => n t0 (right t1 s) end. 

Eval compute in right (n l l) (n l (n l l)).


Theorem ossz_tree : forall t s : tree, length (right t s) = length t + length s.
Proof.
  induction t, s; simpl; auto.
  rewrite IHt2.
  simpl.
  omega.
  rewrite IHt2.
  simpl.
  omega.
Qed.

Theorem ossz_tree_ll : length (right l l) = length l + length l.
Proof.
  apply ossz_tree with (t:=l) (s:=l).
Qed.

Inductive Operator : Set :=
  | Plus : Operator
  | Mult : Operator.


Inductive AST : Set :=
  | leaf : nat -> AST
  | node : Operator -> AST -> AST -> AST.


Check node Plus (node Mult (leaf 2) (leaf 3)) (leaf 6).


Fixpoint evaluation (t : AST) : nat :=
  match t with
    | leaf l' => l'
    | node o t_1 t_2 => match o with
                          | Plus => plus (evaluation t_1) (evaluation t_2)
                          | Mult => mult (evaluation t_1) (evaluation t_2)
                        end
  end.

Inductive UBTree : Set :=
  | leaf0 : UBTree
  | node1 (a: UBTree) : UBTree
  | node2 (a: UBTree) (b: UBTree) : UBTree.

Fixpoint right_UB (t:UBTree) (s:UBTree) : UBTree :=
  match t with
    | leaf0 => node2 leaf0 s
    | node1 a => node1 (right_UB a s)
    | node2 a b => node2 a (right_UB b s)
  end.

Fixpoint length_UB (t: UBTree) : nat :=
  match t with
    | leaf0 => 1
    | node1 a => length_UB a
    | node2 a b => (length_UB a) + (length_UB b)
  end.

Theorem leveltetel: forall s t : UBTree, length_UB(right_UB s t) =  length_UB s + length_UB t.
Proof.
  intros.
  simpl.
  induction s.
  auto.
  auto.
  simpl.
  rewrite IHs2.
  Require Import Omega.
  omega.
Qed.

Inductive bTree : Set :=
  | bleaf : bool -> bTree
  | bnode : (bool -> bool -> bool) -> bTree -> bTree -> bTree.

Check bleaf true.
Check bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true)).

Fixpoint bTree_height (t: bTree) : nat :=
  match t with
    | bleaf x =>  0 (* shall we define this as 1 or as 0? is the height just the number of 'node levels'? *)
    | bnode fn a b => (max (bTree_height a) (bTree_height b)) + 1
  end.

Compute bTree_height (bleaf true).
Compute bTree_height (bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true))).

Fixpoint bTree_mirror (t: bTree) : bTree :=
  match t with
    | bleaf x => bleaf x
    | bnode fn a b => bnode fn (bTree_mirror b) (bTree_mirror a)
  end.

Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

Check hleaf true.
Check hnode 0 andb (hleaf true) (hleaf true).

Fixpoint forgetful (n:nat) (t: hbTree n) : bTree :=
  match t with
    | hleaf b => bleaf b
    | hnode size fn a b => bnode fn (forgetful size a) (forgetful size b)
  end.

Search max.

Theorem magassagtetel : forall (n:nat) (t: hbTree n), bTree_height(forgetful n t) = n. 
Proof.
  induction t.
  induction b.
  compute.
  reflexivity.
  compute.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  assert (H: Init.Nat.max n0 n0 = n0).
  apply Nat.max_id.
  rewrite H.
  omega.
Qed.

Fixpoint hbTree_mirror (n: nat) (t: hbTree n) : hbTree n :=
  match t with
    | hleaf x => hleaf x
    | hnode size fn a b => hnode size fn (hbTree_mirror size b) (hbTree_mirror size a)
  end.

Check hnode 0 andb (hleaf true) (hleaf true).
Check hbTree_mirror 1 (hnode 0 andb (hleaf true) (hleaf true)).









