
## Természetes számok

Ez egy elég kemény dió. Sok csomag és taktika van, ami ezzel küzd: omega, crush, Mathematical Components.

```coq
SearchAbout plus.

Theorem n_plus_O : forall n : nat, n + O = n.
Proof. 
  intros.
  induction n.
  unfold plus.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Show Proof.
Qed.
```

## Fák, bokrok, ligetek

```coq
Inductive tree : Set :=
  | l : tree
  | n : tree -> tree -> tree.

Fixpoint length (t:tree) : nat :=
  match t with
    | l => 1
    | n t1 t2 => (length t1) + (length t2) end. 

Theorem levelhossz : length(l)=1.
Proof. 
  unfold length.
  reflexivity.
Qed.

Fixpoint right (t s : tree) : tree :=
  match t with
    | l => n l s
    | n t0 t1 => n t0 (right t1 s) end. 

Eval compute in right (n l l) (n l (n l l)).

Theorem ossz_tree : forall t s : tree, length (right t s) = length t + length s.
Proof.
  intros.
  induction t.
  simpl.
  reflexivity.
  simpl.
  rewrite IHt2.
  Require Import Omega.
  omega.
Qed.

Theorem ossz_tree_ll : length (right l l) = length l + length l.
Proof.
  apply ossz_tree with (t:=l) (s:=l).
Qed.
```



