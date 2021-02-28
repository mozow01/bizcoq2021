(* ea *)

Inductive szavak : Set :=
  | Hello : szavak -> szavak
  | world : szavak.

(* hf *)

Locate "exists".
Print ex.

Theorem szavak_form_warmup : 
  forall (x : szavak), x = world -> (exists (y : szavak), y = world).
Proof.
  apply ex_intro with (P:=fun x' => x' = world).
Qed.

Theorem szavak_form_warmup_2 : 
  forall (z x: szavak), x = Hello z -> (exists (y : szavak), y = Hello z).
Proof.
  intro z.
  apply ex_intro with (P:=fun x' => x' = Hello z).
Qed.

Theorem szavak_form_warmup_3 : forall (z x: szavak),
  Hello x = Hello z -> (exists (y : szavak), Hello y = Hello z).
Proof.
  intro z.
  apply ex_intro with (P:=fun x' => Hello x' = Hello z).
Qed.

Theorem szavak_form_warmup_4 : forall (z x: szavak),
  Hello z = Hello x -> (exists (y : szavak), Hello z = Hello y).
Proof.
  intro z.
  apply ex_intro with (P:=fun x' => Hello z = Hello x').
Qed.

Theorem szavak_form_warmup_5 : forall (z x: szavak),
  Hello z = Hello x-> (exists (y : szavak), Hello z = Hello y).
Proof.
  intro z.
  intro x.
  apply ex_intro with (P:=fun x' => Hello z = Hello x').
Qed.

Theorem szavak_form_warmup_6 : forall (x: szavak),
  Hello world = Hello x-> (exists (y : szavak), Hello world = Hello y).
Proof.
  intro x.
  apply ex_intro with (P:=fun x' => Hello world = Hello x').
Qed.

Theorem szavak_form_warmup_7 : forall (x: szavak),
  Hello world = Hello x-> (exists (y : szavak), Hello world = Hello y).
Proof.
  intro x.
  intro H.
  revert H.
  apply ex_intro with (P:=fun x' => Hello world = Hello x').
Qed.

Theorem szavak_form : 
  forall (x : szavak), x = world \/ (exists (y : szavak), x = Hello y).
Proof.
  induction x.
  destruct IHx as [IHx1 | IHx2].
  right.
  assert (Hello world = Hello x).
  rewrite IHx1.
  reflexivity.
  revert H.
  rewrite IHx1.
  apply ex_intro with (P:=fun x' => Hello world = Hello x').

  right.
  clear IHx2.
  assert (Hello x = Hello x).
  reflexivity.
  revert H.
  apply ex_intro with (P:=fun x' => Hello x = Hello x').

  left; reflexivity.
  Show Proof.
Qed.
