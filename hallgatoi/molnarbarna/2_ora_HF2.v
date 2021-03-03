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


Theorem szavak_dec_1 : forall (x : szavak), x= world \/ x<>world.
Proof.
  induction x.
  right.
  discriminate.
  left.
  reflexivity.
  Show Proof.
Qed.

Theorem szavak_dec_2 : 
forall (x : szavak), x= Hello world \/ x<>Hello world.
Proof.
  induction x.
  induction x.
  right.
  discriminate.
  left.
  reflexivity.
  right.
  discriminate.
  Show Proof.
Qed.
Print ex.

Theorem szavak_form : 
forall (x : szavak), x= world \/ (exists (y : szavak), x=Hello y).
Proof.
  intros.
  induction x.
  right.
  exists x.
  reflexivity.
  left.
  reflexivity.
Qed.
  
  
  