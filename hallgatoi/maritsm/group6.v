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

Inductive Z6 : Set :=
|z0 : Z6
|z1 : Z6
|z2 : Z6
|z3 : Z6
|z4 : Z6
|z5 : Z6.

Definition Z6_succ (x:Z6) : Z6 :=
match x with
| z0 => z1
| z1 => z2
| z2 => z3
| z3 => z4
| z4 => z5
| z5 => z0
end.

Definition Z6_add (x : Z6) (y : Z6) : Z6 :=
match x with
|z0 => y
|z1 => Z6_succ y
|z2 => Z6_succ (Z6_succ y)
|z3 => Z6_succ (Z6_succ (Z6_succ y))
|z4 => Z6_succ (Z6_succ (Z6_succ (Z6_succ y)))
|z5 => Z6_succ (Z6_succ (Z6_succ (Z6_succ (Z6_succ y))))
end.

Definition Z6_inv (x:Z6) : Z6 :=
match x with
| z0 => z0
| z1 => z5
| z2 => z4
| z3 => z3
| z4 => z2
| z5 => z1
end.


Theorem Z6_group : Group.
Proof.
  apply (const_kozos Z6 Z6_add Z6_inv z0).
  induction a,b,c ; auto.
  induction a; auto.
  induction a; auto.
  Show Proof.
Defined.
