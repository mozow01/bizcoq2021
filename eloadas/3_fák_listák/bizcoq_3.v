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














