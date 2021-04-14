Fixpoint elsonfvsum (n:nat)(f:nat->nat):nat:=
  match n with
  | 0 => 0
  | S(n0) => elsonfvsum(n0)(f) +f (S(n0))
  end.

Definition fv1(k:nat):=
  k+k.


Definition alap (k:nat):=
  k.

Eval compute in elsonfvsum 3 fv1.

Theorem lemma (n:nat): n * (n + 1) + 2 * S n = S n * (S n + 1).
Proof.
  induction n.
  compute;auto.
  
  simpl (S(n) + 1).
  simpl (2 * S(S n)).
  simpl.
  Require Import Omega.
  Require Import Lia.
  lia.
Qed.
Theorem gauss: forall n:nat, 2*(elsonfvsum n alap) = n*(n+1).
  intros.
  induction n.
  compute.
  auto.
  simpl (elsonfvsum (S n) alap).
  enough (2 * (elsonfvsum n alap + alap (S n)) = 2 * (elsonfvsum n alap) + 2*alap (S n)).
  rewrite H.
  rewrite IHn.
  unfold alap.
  induction n.
  compute.
  auto.
  Require Import Lia.
  lia.
  lia.
Qed.
   