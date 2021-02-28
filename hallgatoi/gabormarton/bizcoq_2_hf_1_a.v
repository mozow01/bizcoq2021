(* ea *)

Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.

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

Theorem Z_3_eq_dec_mod : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y.
  left. 
  reflexivity. 
  right. 
  discriminate.

  right. 
  discriminate.
  right. 
  discriminate.
  left. 
  reflexivity. 
  right. 
  discriminate.
  right. 
  discriminate.
  right. 
  discriminate.
  left. 
  reflexivity. 
Qed.


(* hf *)

Theorem Z_3_eq_dec_mod_v2 : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto.
  right; discriminate.
  right; discriminate.
  right; discriminate.
  right; discriminate.
  right; discriminate.
  right; discriminate.
Qed.
