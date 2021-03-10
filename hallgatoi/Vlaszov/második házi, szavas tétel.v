(*
Z_3 háromelemű (véges) típus, Z_3={0, 1, 2} ill. {n, a, b}
*)

Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.

(*
Legyen belőle csoport, ami egy olyan algebrai struktúra, ahol van 
op: G->G->G művelet, 
ahol op asszociatív,
van z neutrális elem: op z x = x = op x z
van inv: inverz : op x (inv) x = z = op (inv x) x
Z_3-ban ez az összeadás:
*)

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

(*Absztrakt csoport definíciója Structure vagy Record környezettel: *)

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


(*Z_3 a műveletekkel valóban csoport, amit
 a Group típus Z_3_group jelölésű eleme mutat, aminek a definíciója: *)

Theorem Z_3_group : Group.
Proof.
  apply (const_kozos Z_3 ope inve n).
  induction a0, b0, c; compute; auto.
  induction a0; auto.
  induction a0; auto.
Defined.

(*Minden véges típus algoritmikusan eldönthető, így Z_3 is: *)

Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
  Show Proof.
Defined.

(*A morfizmusok őshonos állatfajok a típuselméletben, 
így a csoportok közötti G->H művelettartó leképezések is *)

Definition GroupMorphism (G:Group) (H:Group) (f:G->H) : Prop :=  
    f(z G)=z H /\
    forall a:G, f(inv G a)=inv H (f(a)) /\
    forall a b : G, f(op G a b) = op H (f(a)) (f(b)).

(*Pl. a Z_1->Z_3, e|--->n leképezés is egy csoportmorfizmus *)


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

Inductive Z_6 : Set :=
  |z0 : Z_6
  |z1 : Z_6
  |z2 : Z_6
  |z3 : Z_6
  |z4 : Z_6
  |z5 : Z_6.

Definition inve6 (x:Z_6) :=
  match x with
  | z0 => z0
  | z1 => z5
  | z2 => z4
  | z3 => z3
  | z4 => z2
  | z5 => z1
  end.

(*Ezt Marits Marcitól csentem el, hogy teljes legyen a file.*)
Definition Z6_succ (x:Z_6) : Z_6 :=
match x with
  | z0 => z1
  | z1 => z2
  | z2 => z3
  | z3 => z4
  | z4 => z5
  | z5 => z0
  end.

Definition Z6_add (x : Z_6) (y : Z_6) : Z_6 :=
match x with
  |z0 => y
  |z1 => Z6_succ y
  |z2 => Z6_succ (Z6_succ y)
  |z3 => Z6_succ (Z6_succ (Z6_succ y))
  |z4 => Z6_succ (Z6_succ (Z6_succ (Z6_succ y)))
  |z5 => Z6_succ (Z6_succ (Z6_succ (Z6_succ (Z6_succ y))))
  end.

Theorem Z_3_eq_dec_mod : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
Defined.

Inductive szavak : Set :=
   | Hello : szavak -> szavak
   | world : szavak.

Definition mondat_1 : szavak.
  constructor 1.
  constructor 2.
  Show Proof.
Defined.

Definition mondat_2 : szavak.
  apply Hello.
  apply world.
Defined.

Theorem szavak_dec_1 : forall (x : szavak), x = world \/ x<>world.
  intros.
  induction x.
  right.
  discriminate.
  left.
  reflexivity.
  Show Proof.
Qed.
