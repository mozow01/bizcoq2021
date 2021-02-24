Search bool.
Print andb.

Definition f_1 (g: bool -> bool) : bool :=
  match g(true) with
  | true => g(false)
  | false => false
  end.

Eval compute in f_1(fun x : bool => orb x (negb x)).

Definition f_2 (g: bool -> bool -> bool) : bool :=
  match f_1(g(true)) with
  | true => f_1(g(false))
  | false => false
  end.

Eval compute in f_2(fun x y : bool => orb x y).
Eval compute in f_2(fun x y : bool => implb (orb (negb x) (negb y)) (negb (andb x y)) ).

Search nat.

Fixpoint f (n: nat) (g: bool -> bool) {struct n} : bool :=
match n with
| 0 => false
| 1 => andb (g false) (g true)
| S p => f p g
end.

Eval compute in f 1 (fun x y : bool => orb x y).

 
