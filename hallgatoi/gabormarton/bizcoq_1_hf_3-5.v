(* hf 3 *)

Definition f_1 (g: bool -> bool) : bool := andb (g(true)) (g(false)).
Compute f_1(fun x : bool => orb x (negb x)).


(* hf 4 *)

Inductive szavak : Set :=
  | Hello : szavak -> szavak
  | world : szavak.
Compute Hello world.

Inductive Szavak : Set :=
  | hello : Szavak
  | World : Szavak.
Compute (hello, World).


(* hf 5 *)

Definition f_2 (g: bool -> bool -> bool) : bool := andb (f_1(g(true))) (f_1(g(false))).
Compute (f_2(fun x y => orb x y)).
Compute (f_2(fun x y => implb (orb (negb x) (negb y)) (negb (andb x y)))). 