Structure Hatcsucsu : Type := make_Hatcsucsu
{
  n :> nat;

  E'' :> nat -> nat -> bool ;

  hatcsucsu : n = 6;
  undirected'' : forall (a : nat) (b : nat), (a < 6 /\ b < 6) -> implb (E'' a b) (E'' b a) = true;
  noloop'' : forall (a : nat), (a < 6) -> negb (E'' a a) = true;
}.
Require Import Bool.
Require Import Notations Logic Datatypes.
Require Decimal Hexadecimal Number.
Local Open Scope nat_scope.
Require Import Arith.
Print Arith.
Fixpoint sum_to (n:nat) : nat :=
  match n with
  | 0 => 0
  | S k => n + sum_to k
  end.
Eval compute in sum_to 6.

Definition elek1 (a:nat)(b:nat):bool:=
  match a,b with
    | 0,1 => true
    | 1,0 => true
    | 0,2 => true
    | 2,0 => true
    | 0,3 => true
    | 0,5 => true
    | 3,0 => true
    | 5,0 => true
    | _,_ => false
    end.

Definition rossz:Hatcsucsu.
  apply (make_Hatcsucsu 6 elek1).
  auto.
  compute.
  induction a;compute;auto;auto.
  induction b.
  auto.
  induction b.
  auto.
  induction b;auto.
  auto.
  induction b;auto;auto.
  induction b;auto;auto.
  induction b;auto;auto.
  induction b;auto;auto.
  induction a;auto.
  auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a,b;auto;auto.
  induction a;auto;auto.
  induction a;auto;auto.
  induction a;auto;auto.
  induction a;auto;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
  induction a;auto.
Defined.



Definition sajatif (b:bool)(n:nat)(k:nat):=
  match b with
  | true => n
  | false => k
  end.

Eval compute in sajatif true 1 6.

Definition nkval (G:Hatcsucsu)(n:nat)(k:nat) :=
  sajatif(E'' G n k) (1)(0).

Eval compute in nkval rossz 0 5.

Definition fokszam (G:Hatcsucsu)(a:nat):nat:=
  (nkval G a 0)+(nkval G a 1)+(nkval G a 2)+(nkval G a 3)+(nkval G a 4)+(nkval G a 5).

Eval compute in fokszam rossz 4.

Theorem egyenlo(a:bool)(b:bool): ((implb(a)(b)=true) /\ (implb(b)(a))=true)-> a=b.
  intros.
  induction a,b;auto.  
  destruct H.
  discriminate.
  destruct H.
  discriminate.
Qed.



Theorem elekodavissza: forall (G1:Hatcsucsu),forall (a:nat) (b:nat), (a < 6 /\ b < 6) ->E'' G1 a b = E'' G1 b a.
  intros.
  enough (implb (E'' G1 a b) (E'' G1 b a) = true).
  enough (implb(E'' G1 b a) (E'' G1 a b) = true).
  apply (egyenlo (E'' G1 a b)(E'' G1 b a)).
  rewrite H0.
  rewrite H1.
  auto.
  rewrite undirected''.
  auto.
  destruct H.
  split.
  apply H1.
  apply H.
  rewrite undirected''.
  auto.
  apply H.
Defined.




Definition fokszamossz (G:Hatcsucsu):=
   nkval G 0 0 + (nkval G 0 1 + nkval G 1 0) + (nkval G 0 2 + nkval G 2 0) +
   (nkval G 0 3 + nkval G 3 0) + (nkval G 0 4 + nkval G 4 0) + (nkval G 0 5 + nkval G 5 0) +
    nkval G 1 1 +
   (nkval G 1 2 + nkval G 2 1) + (nkval G 1 3 + nkval G 3 1) + (nkval G 1 4 +
    nkval G 4 1) +
   (nkval G 1 5 + nkval G 5 1) + nkval G 2 2 + (nkval G 2 3 + nkval G 3 2) +
    (nkval G 2 4 +
   nkval G 4 2) + (nkval G 2 5 + nkval G 5 2) + nkval G 3 3 + (nkval G 3 4 +
    nkval G 4 3) + (nkval G 3 5 + nkval G 5 3) + nkval G 4 4 + (nkval G 4 5 + nkval G 5 4) +
    nkval G 5 5.

Eval compute in fokszamossz rossz.

Fixpoint paros n : bool :=
  match n with
    | 0 => true
    | S n' => negb(paros n')
  end.

Theorem S_1: forall n:nat, n+1=S n.
  intros.
  induction n0.
  auto. 
  simpl.
  rewrite IHn0.
  auto.
Defined.
Require Import Coq.Bool.Bool.

Lemma paros_ad m n :
  paros (m + n) = negb (xorb (paros m) (paros n)).
  Proof.
  induction m.
  simpl.
  -destruct (paros n);compute;auto.
  -simpl. rewrite IHm. now destruct (paros m); destruct (paros n).
Qed.

Lemma parosszorz m n:
  paros(m*n)=paros m || paros n.
Proof.
  induction m;auto;simpl.
  rewrite paros_ad.
  rewrite IHm.
  now destruct (paros m); destruct (paros n).
Qed.

Theorem ketszervalamiazparos: forall n:nat, paros(2*n)=true.
Proof.
  intros.
  rewrite parosszorz.
  auto.
Qed.

Definition elszam (G:Hatcsucsu):=
  fokszamossz G/2.

Eval compute in elszam rossz.

Require Import Omega.



Theorem szer2_egymegegy(n:nat): n+n = 2 * n.
  induction n;auto.
  simpl.
  
  omega.
Qed.


Theorem nullmegval: forall n:nat, n+0=n.
  auto.
Qed.

Theorem valmegnull: forall n:nat, 0+n=n.
  auto.
Qed.



Theorem nullmegnull: 0=0+0.
  auto.
Qed.

Theorem egyrend: forall a b c:nat, a+b=c+b -> a=c.
Proof.
  intros.
  induction a,b,c;compute;auto.
  rewrite nullmegnull.
  rewrite H.
  auto with arith.
  Require Import Omega.
  omega.
  omega.
  omega.
  omega.
  omega.
Defined.

Theorem egyetatir(k:nat):forall F:Hatcsucsu,forall b:nat,(k < 6 /\ b < 6) -> E'' F k b = E'' F b k.
  intros.
  rewrite elekodavissza.
  auto.
  apply H.
Qed.

Theorem nkvalokra(a:nat): forall G:Hatcsucsu, forall b:nat, (a < 6 /\ b < 6) -> nkval G a b = nkval G b a.
  intros.
  unfold nkval.
  unfold sajatif.
  rewrite elekodavissza.
  auto.
  apply H.
Qed.

Require Import PeanoNat.

Check PeanoNat.Nat.add_assoc.



Theorem osszegbolketszer(n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15:nat):
0 + 2 * n1 + 2 * n2 + 2 * n3 + 2 * n4 + 2 * n5 +
  0 + 2 * n6 + 2 * n7 + 2 * n7 + 2 * n9 + 0 +
  2 * n10 + 2 * n11 + 2 * n12 + 2 * n13 + 
  2 * n14 + 0 + 2 * n15 + 0 = 2 * (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 +n10 + n11 + n12 + n13 + n14 + n15).
Proof.
  Require Import Lia.
  rewrite nullmegval.
  repeat rewrite nullmegval.
  rewrite valmegnull.
  simpl.
  repeat rewrite nullmegval.
  lia.
  auto.
  
  auto.
  lia.
  omega.
  
  lia.
  enough
  compute.
  rewrite szer2_egymegegy.
  omega.
  simpl.
  auto with arith.
  reflexivity.
  induction n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15.
  compute.   

Theorem nk:forall G:Hatcsucsu, exists k:nat, fokszamossz G=2*k.
intros.
unfold fokszamossz.
  unfold fokszam.
  enough (nkval G 0 1 + nkval G 1 0 = 2*nkval G 0 1).
  rewrite H.
  enough (nkval G 0 2 + nkval G 2 0 = 2*nkval G 0 2).
  enough (nkval G 0 3 + nkval G 3 0 = 2*nkval G 0 3).
  enough (nkval G 0 4 + nkval G 4 0 = 2*nkval G 0 4).
  enough (nkval G 0 5 + nkval G 5 0 = 2*nkval G 0 5).
  enough (nkval G 1 2 + nkval G 2 1 = 2*nkval G 1 2).
  enough (nkval G 1 3 + nkval G 3 1 = 2*nkval G 1 3).
  enough (nkval G 1 4 + nkval G 4 1 = 2*nkval G 1 4).
  enough (nkval G 1 5 + nkval G 5 1 = 2*nkval G 1 5).
  enough (nkval G 2 3 + nkval G 3 2 = 2*nkval G 2 3).
  enough (nkval G 2 4 + nkval G 4 2 = 2*nkval G 2 4).
  enough (nkval G 2 5 + nkval G 5 2 = 2*nkval G 2 5).
  enough (nkval G 3 4 + nkval G 4 3 = 2*nkval G 3 4).
  enough (nkval G 3 5 + nkval G 5 3 = 2*nkval G 3 5).
  enough (nkval G 4 5 + nkval G 5 4 = 2*nkval G 4 5).
  rewrite H0.
  rewrite H4.
  rewrite H5.
  rewrite H6.
  rewrite H7.
  rewrite H8.
  rewrite H9.
  rewrite H10.
  rewrite H11.
  rewrite H12.
  rewrite H13.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  enough (nkval G 0 0 = 0).
  rewrite H14.
  enough (nkval G 1 1 = 0).
  enough (nkval G 2 2 = 0).
  enough (nkval G 3 3 = 0).
  enough (nkval G 4 4 = 0).
  enough (nkval G 5 5 = 0).
  rewrite H15.
  rewrite H16.
  rewrite H17.
  rewrite H18.
  rewrite H19.


  apply (szer2_egymegegy (nkval G 0 1)).
  unfold paros.

Theorem fokszamosszparos: forall G:Hatcsucsu, paros(fokszamossz G)=true.
Proof.
  intros.
  unfold fokszamossz.
  unfold fokszam.
  rewrite (nkvalokra 5).
  rewrite (nkvalokra 4).
  rewrite (nkvalokra 3).
  unfold paros.
  
  
  rewrite (szer2_egymegegy (nkval G 0 1)).


Theorem fokok_ketszer:forall G:Hatcsucsu, fokszamossz G=elszam G*2.
  intros.
  unfold elszam.
  Require Import Omega.
  rewrite nkval_ugyanaz.
  
  
  

Theorem fokszamosszegparos:forall G:Hatcsucsu, paros (fokszamossz G)=true.
Proof.
  enough (~ exists G0:Hatcsucsu, paros (fokszamossz G0) = false).
  enough (forall G:Hatcsucsu, paros (fokszamossz G)=true).
  contradiction.
  induction (fokszamossz G).
  auto.
  
  contradiction.
  
  compute;auto. 








