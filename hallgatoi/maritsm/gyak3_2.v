(*Require Import Arith.*)

Inductive bTree : Set :=
| bleaf : bool -> bTree
| bnode : (bool -> bool -> bool) -> bTree -> bTree -> bTree.

Fixpoint height (b : bTree) : nat :=
match b with
| bleaf x => 1
| bnode g b1 b2 => (max (height b1) (height b2)) + 1
end.

Eval compute in height( bnode orb (bleaf true) (bnode andb (bleaf true)(bleaf false)) ).

Fixpoint mirror (b : bTree) : bTree :=
match b with
| bleaf x => bleaf x
| bnode g b1 b2 => bnode g (mirror b2) (mirror b1)
end.

Check mirror( bnode orb (bleaf true) (bnode andb (bleaf true)(bleaf false)) ).

(* copy *)
Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

(* pl.: *)

Check hleaf true.
Check hnode 0 andb (hleaf true) (hleaf true).
(* /copy *)

Fixpoint forgetful (n:nat) (t: hbTree n) : bTree :=
match t with
| hleaf x => bleaf x
| hnode n g h1 h2 => bnode g (forgetful (n) h1) (forgetful (n) h2)
end.

Eval compute in forgetful 1 ( hnode 0 andb (hleaf true) (hleaf true)).
