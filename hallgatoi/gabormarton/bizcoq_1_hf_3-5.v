(* hf 3 *)

Definition f_1 (g: bool -> bool) : bool := andb (g(true)) (g(false)).
Eval compute in f_1(fun x : bool => orb x (negb x)).


(* hf 4 *)

Inductive szavak : Set :=
  | Hello : szavak -> szavak
  | world : szavak.
Eval compute in Hello world.

Inductive Szavak : Set :=
  | hello : Szavak
  | World : Szavak.
Eval compute in (hello, World).


(* hf 5 *)

Definition f_2 (g: bool -> bool -> bool) : bool := andb (f_1(g(true))) (f_1(g(false))).
Eval compute in (f_2(fun x y => orb x y)).
Eval compute in (f_2(fun x y => implb (orb (negb x) (negb y)) (negb (andb x y)))).
