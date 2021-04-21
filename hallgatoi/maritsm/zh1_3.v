Structure Hatcsucsu : Type := make_Hatcsucsu
{
  n :> nat;

  E:> nat -> nat -> bool ;

  hatcsucsu : n = 6;
  undirected : forall (a : nat) (b : nat), (a < 6 /\ b < 6) -> implb (E a b) (E b a) = true;
  noloop : forall (a : nat), (a < 6) -> E a a = false;
}.

(* a *)

Definition boolToNat (b:bool) : nat :=
match b with
| true => 1
| false => 0
end.

Definition csucsFokSzam (n:nat) (h:Hatcsucsu) : nat :=
(boolToNat (E h n 0)) + (boolToNat (E h n 1)) + (boolToNat (E h n 2)) +
(boolToNat (E h n 3)) + (boolToNat (E h n 4)) + (boolToNat (E h n 5)).



(* b *)

Definition csucsFokszamOsszeg (h:Hatcsucsu) : nat :=
(csucsFokSzam 0 h) + (csucsFokSzam 1 h) + (csucsFokSzam 2 h) +
(csucsFokSzam 3 h) + (csucsFokSzam 4 h) + (csucsFokSzam 5 h).

(* c *)

Require Import Arith.
Require Import Lia.
Require Import Bool.

Check noloop.
Check undirected.

Lemma boolImpLemma : forall (a: bool) (b:bool), implb a b = true /\ implb b a = true <-> a=b.
Proof.
  intros.
  split.
  induction a.
  rewrite implb_true_r.
  rewrite implb_true_l.
  intuition.
  rewrite implb_false_r.
  rewrite implb_false_l.
  intuition.
  apply negb_true_iff in H1.
  intuition.
  
  split.
  rewrite H.
  apply implb_same.
  rewrite H.
  apply implb_same.
Defined.

Theorem fokSzamOsszeg_paros : forall (h:Hatcsucsu), exists k: nat, csucsFokszamOsszeg h = 2*k.
Proof.
  intros.
  unfold csucsFokszamOsszeg.
  unfold csucsFokSzam.
  assert ((h 0 0) = false) as H00.
  apply noloop.
  lia.
  assert ((h 1 1) = false) as H11.
  apply noloop.
  lia.
  assert ((h 2 2) = false) as H22.
  apply noloop.
  lia.
  assert ((h 3 3) = false) as H33.
  apply noloop.
  lia.
  assert ((h 4 4) = false) as H44.
  apply noloop.
  lia.
  assert ((h 5 5) = false) as H55.
  apply noloop.
  lia.
  rewrite H00, H11, H22, H33, H44, H55.
  
  assert (h 0 1 = h 1 0) as H01.
  rewrite <- boolImpLemma with (a:=h 0 1) (b:=h 1 0).
  split.
  apply undirected with (a:=0) (b:=1).
  lia.
  apply undirected with (a:=1) (b:=0).
  lia.
  assert (h 0 2 = h 2 0) as H02.
  rewrite <- boolImpLemma with (a:=h 0 2) (b:=h 2 0).
  split.
  apply undirected with (a:=0) (b:=2).
  lia.
  apply undirected with (a:=2) (b:=0).
  lia.
  assert (h 0 3 = h 3 0) as H03.
  rewrite <- boolImpLemma with (a:=h 0 3) (b:=h 3 0).
  split.
  apply undirected with (a:=0) (b:=3).
  lia.
  apply undirected with (a:=3) (b:=0).
  lia.
  assert (h 0 4 = h 4 0) as H04.
  rewrite <- boolImpLemma with (a:=h 0 4) (b:=h 4 0).
  split.
  apply undirected with (a:=0) (b:=4).
  lia.
  apply undirected with (a:=4) (b:=0).
  lia.
  assert (h 0 5 = h 5 0) as H05.
  rewrite <- boolImpLemma with (a:=h 0 5) (b:=h 5 0).
  split.
  apply undirected with (a:=0) (b:=5).
  lia.
  apply undirected with (a:=5) (b:=0).
  lia.
  assert (h 1 2 = h 2 1) as H12.
  rewrite <- boolImpLemma with (a:=h 1 2) (b:=h 2 1).
  split.
  apply undirected with (a:=1) (b:=2).
  lia.
  apply undirected with (a:=2) (b:=1).
  lia.
  assert (h 1 3 = h 3 1) as H13.
  rewrite <- boolImpLemma with (a:=h 1 3) (b:=h 3 1).
  split.
  apply undirected with (a:=1) (b:=3).
  lia.
  apply undirected with (a:=3) (b:=1).
  lia.
  assert (h 1 4 = h 4 1) as H14.
  rewrite <- boolImpLemma with (a:=h 1 4) (b:=h 4 1).
  split.
  apply undirected with (a:=1) (b:=4).
  lia.
  apply undirected with (a:=4) (b:=1).
  lia.
  assert (h 1 5 = h 5 1) as H15.
  rewrite <- boolImpLemma with (a:=h 1 5) (b:=h 5 1).
  split.
  apply undirected with (a:=1) (b:=5).
  lia.
  apply undirected with (a:=5) (b:=1).
  lia.
  assert (h 2 3 = h 3 2) as H23.
  rewrite <- boolImpLemma with (a:=h 2 3) (b:=h 3 2).
  split.
  apply undirected with (a:=2) (b:=3).
  lia.
  apply undirected with (a:=3) (b:=2).
  lia.
  assert (h 2 4 = h 4 2) as H24.
  rewrite <- boolImpLemma with (a:=h 2 4) (b:=h 4 2).
  split.
  apply undirected with (a:=2) (b:=4).
  lia.
  apply undirected with (a:=4) (b:=2).
  lia.
  assert (h 2 5 = h 5 2) as H25.
  rewrite <- boolImpLemma with (a:=h 2 5) (b:=h 5 2).
  split.
  apply undirected with (a:=2) (b:=5).
  lia.
  apply undirected with (a:=5) (b:=2).
  lia.
  assert (h 3 4 = h 4 3) as H34.
  rewrite <- boolImpLemma with (a:=h 3 4) (b:=h 4 3).
  split.
  apply undirected with (a:=3) (b:=4).
  lia.
  apply undirected with (a:=4) (b:=3).
  lia.
  assert (h 3 5 = h 5 3) as H35.
  rewrite <- boolImpLemma with (a:=h 3 5) (b:=h 5 3).
  split.
  apply undirected with (a:=3) (b:=5).
  lia.
  apply undirected with (a:=5) (b:=3).
  lia.
  assert (h 4 5 = h 5 4) as H45.
  rewrite <- boolImpLemma with (a:=h 4 5) (b:=h 5 4).
  split.
  apply undirected with (a:=4) (b:=5).
  lia.
  apply undirected with (a:=5) (b:=4).
  lia.
  (* ez kegyetlen volt :) *)
  rewrite H01, H02, H03, H04, H05, H12, H13, H14, H15, H23, H24, H25, H34, H35, H45.
  
  (* finale *)
  
  exists (boolToNat (h 1 0) +
            boolToNat (h 2 0) +
            boolToNat (h 3 0) +
            boolToNat (h 4 0) +
            boolToNat (h 5 0) +
            boolToNat (h 2 1) +
            boolToNat (h 3 1) +
            boolToNat (h 4 1) +
            boolToNat (h 5 1) +
            boolToNat (h 3 2) +
            boolToNat (h 4 2) +
            boolToNat (h 5 2) +
            boolToNat (h 4 3) +
            boolToNat (h 5 3) +
            boolToNat (h 5 4)).
  assert (boolToNat false = 0) as duh.
  simpl; reflexivity.
  rewrite duh.
  lia.
Defined.

