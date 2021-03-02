(* ea *)

Inductive szavak : Set :=
  | Hello : szavak -> szavak
  | world : szavak.

Theorem szavak_dec_1 : forall (x : szavak), x = world \/ x <> world.
  induction x; auto; right; discriminate.
  Show Proof.
Qed.


(* hf *)

Theorem szavak_dec_2 : forall (x : szavak), x = Hello world \/ x <> Hello world.
Proof.
  intro x.
  destruct x.
  destruct x.
  right.
  discriminate.
  left.
  reflexivity.
  right.
  discriminate.
  Show Proof.
Qed.

Theorem szavak_cons_inj : forall (x y: szavak), x <> y -> Hello x <> Hello y.
Proof.
  intros x y H.
  (* A *)
  assert (x = y -> False).
  intuition.
  intros abs.
  injection abs.
  assumption.
  (* B *)
  (*
  intuition.
  injection H0.
  assumption.
  *)
  Show Proof.
Qed.

Theorem szavak_dec_2_v2 : forall (x : szavak), x = Hello world \/ x <> Hello world.
Proof.
  induction x.
  destruct IHx as [IHx1 | IHx2].
  right.
  rewrite IHx1.
  discriminate.

  assert (x = world \/ x <> world).
  apply szavak_dec_1.
  destruct H as [H1 | H2].
  left.
  rewrite H1.
  reflexivity.
  right.
  apply szavak_cons_inj.
  assumption.
  right.
  discriminate.
  Show Proof.
Qed.
