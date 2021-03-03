Inductive Z_6 : Set :=
  | a : Z_6
  | s : Z_6
  | d : Z_6
  | f : Z_6
  | g : Z_6
  | h : Z_6.

Definition ope x y :=
 match x, y with
  | a , y => y
  | x , a => x
  | s , d => f
  | s , s => d
  | s , f => g
  | s , g => h
  | s , h => a
  | d , s => f
  | d , d => g
  | d , f => h
  | d , g => a
  | d , h => s
  | f , s => g
  | f , d => h
  | f , f => a
  | f , g => s
  | f , h => d
  | g , s => h
  | g , d => a
  | g , f => s
  | g , g => d
  | g , h => f
  | h , s => a
  | h , d => s
  | h , f => d
  | h , g => f
  | h , h => g
  end.

Definition inve x:=
  match x with
  | a => a
  | s => h
  | d => g
  | f => f
  | g => d
  | h => s
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

Theorem Z_6_group : Group.
Proof.
  apply(const_kozos Z_6 ope inve a).
  induction a0, b, c; auto.
  induction a0; auto.
  induction a0; auto.
Defined.