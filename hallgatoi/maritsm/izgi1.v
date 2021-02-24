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

Require Import Coq.Lists.List.

Definition si_true : list bool := cons true nil.
Definition si_false : list bool := cons false nil.

Fixpoint f (n: nat) (g: list bool -> bool) {struct n} : bool :=
match n with
| 0 => false
| 1 => andb (g (cons true nil)) (g (cons false nil))
| S p => andb (f p (fun x => g (app x si_true)) ) (f p (fun x => g (app x si_false)) )
end.

Eval compute in f 1 (fun x => orb (nth 1 x false) (negb (nth 1 x false))).
(* az "nth 1 x false" rész a "list bool" típusból bool-ba konvertáláshoz kell *)

Eval compute in f 2 (fun x => orb (nth 1 x false) (nth 2 x false)).
Eval compute in f 2 (fun x => implb (orb (negb (nth 1 x false)) (negb (nth 2 x false)))
                      (negb (andb (nth 1 x false) (nth 2 x false))) ).



 
