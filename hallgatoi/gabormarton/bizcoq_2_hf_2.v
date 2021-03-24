(* ea *)

Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.

Definition ope (x:Z_3) (y:Z_3) :=
  match x , y with
  | n , y => y
  | x , n => x
  | a , b => n
  | b , a => n 
  | a , a => b
  | b , b => a
  end.

Definition inve (x:Z_3) :=
  match x with
  | n => n
  | a => b
  | b => a
  end.

Structure Group : Type := const_kozos
{
  A :> Set;

  op : A -> A -> A ;
  inv : A -> A ;
  z : A ;

  op_assoc : forall a b c, op a (op b c) = op (op a b) c;
  op_z : forall a, op a z = a /\ op z a = a ;
  op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
}.

Theorem Z_3_group : Group.
Proof.
  apply (const_kozos Z_3 ope inve n).
  induction a0, b0, c; compute; auto.
  induction a0; auto.
  induction a0; auto.
Defined.

Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
  Show Proof.
Defined.

Definition GroupMorphism (G:Group) (H:Group) (f:G->H) : Prop :=  
    f(z G)=z H /\
    forall a:G, f(inv G a)=inv H (f(a)) /\
    forall a b : G, f(op G a b) = op H (f(a)) (f(b)).

Inductive Z_1 : Set :=
  | e : Z_1.

Definition ope_1 (x:Z_1) (y:Z_1) :=
  match x , y with
  | e , e => e
  end.

Definition inve_1 x:Z_1 :=
  match x with
  | e => e
  end.

Theorem Z_1_group : Group.
Proof.
  apply (const_kozos Z_1 ope_1 inve_1 e).
  induction a0, b0, c; compute; auto.
  induction a0; auto. 
  induction a0; auto.
Defined.

Definition f_Z_1_Z_3 : Z_1->Z_3 := fun (x:Z_1) => match x with e => n end.

Theorem f_Z_1_Z_3_csoportmorfizmus : GroupMorphism (Z_1_group) (Z_3_group) f_Z_1_Z_3.
Proof.
  unfold GroupMorphism.
  split.
  compute; auto.
  split.
  induction a0.
  compute; auto.
  induction a0, b0.
  induction a0.
  compute; auto.
Qed.


(* hf *)

Inductive Z_6 : Set :=
  | z_6_0 : Z_6 
  | z_6_1 : Z_6 
  | z_6_2 : Z_6 
  | z_6_3 : Z_6 
  | z_6_4 : Z_6 
  | z_6_5 : Z_6.

Definition Z_6_s (x:Z_6) :=
  match x with
    | z_6_0 => z_6_1
    | z_6_1 => z_6_2
    | z_6_2 => z_6_3
    | z_6_3 => z_6_4
    | z_6_4 => z_6_5
    | z_6_5 => z_6_0
  end.

Fixpoint Z_6_iter (n:nat) (f:Z_6 -> Z_6) (x:Z_6) :=
  match n with
    | 0 => x
    | S p => Z_6_iter p f (f x)
  end.

Eval compute in Z_6_iter 0 Z_6_s (z_6_0).
Eval compute in Z_6_iter 1 Z_6_s (z_6_0).
Eval compute in Z_6_iter 6 Z_6_s (z_6_0).
Eval compute in Z_6_iter 9 Z_6_s (z_6_5).

Definition Z_6_op (x:Z_6) (y:Z_6) :=
  match y with
    | z_6_0 => Z_6_iter 0 Z_6_s x
    | z_6_1 => Z_6_iter 1 Z_6_s x
    | z_6_2 => Z_6_iter 2 Z_6_s x
    | z_6_3 => Z_6_iter 3 Z_6_s x
    | z_6_4 => Z_6_iter 4 Z_6_s x
    | z_6_5 => Z_6_iter 5 Z_6_s x
  end.

Eval compute in Z_6_op z_6_0 z_6_0.
Eval compute in Z_6_op z_6_1 z_6_2.
Eval compute in Z_6_op z_6_3 z_6_4.

Definition Z_6_inv (x:Z_6) :=
  match x with
    | z_6_0 => z_6_0
    | z_6_1 => z_6_5
    | z_6_2 => z_6_4
    | z_6_3 => z_6_3
    | z_6_4 => z_6_2
    | z_6_5 => z_6_1
  end.

Theorem Z_6_group : Group.
Proof.
  apply (const_kozos Z_6 Z_6_op Z_6_inv z_6_0).
  induction a0, b0, c; compute; auto.
  induction a0; auto.
  induction a0; auto.
Defined.


Definition f_Z_6_Z_3 : Z_6 -> Z_3 := fun (x:Z_6) =>
  match x with
    | z_6_0 => n
    | z_6_1 => a
    | z_6_2 => b
    | z_6_3 => n
    | z_6_4 => a
    | z_6_5 => b
  end.

Theorem f_Z_6_Z_3_gm : GroupMorphism (Z_6_group) (Z_3_group) f_Z_6_Z_3.
Proof.
  unfold GroupMorphism.
  split.
  compute; auto.
  split.
  induction a0; compute; auto.
  induction a1, b0; compute; auto.
Qed.


Definition f_Z_6_Z_1 : Z_6 -> Z_1 := fun (x:Z_6) =>
  match x with
    | z_6_0 => e
    | z_6_1 => e
    | z_6_2 => e
    | z_6_3 => e
    | z_6_4 => e
    | z_6_5 => e
  end.

Theorem f_Z_6_Z_1_gm : GroupMorphism (Z_6_group) (Z_1_group) f_Z_6_Z_1.
Proof.
  unfold GroupMorphism.
  split.
  compute; auto.
  split.
  induction a0; compute; auto.
  induction a1, b0; compute; auto.
Qed.
