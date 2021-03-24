(* ea *)

Inductive szavak : Set :=
  | Hello : szavak -> szavak
  | world : szavak.

(* hf *)

Theorem szavak_dec_1 : forall (x : szavak), x = world \/ x <> world.
  induction x; auto; right; discriminate.
  Show Proof.
Qed.
