Inductive bTree : Set :=
  | bleaf : bool -> bTree
  | bnode : (bool -> bool -> bool) -> bTree -> bTree -> bTree.

Check bleaf true.
Check bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true)).

(* a *)

Fixpoint height (t:bTree) : nat :=
  match t with
    | bleaf b => 1
    | bnode o bl br => 1 + max (height bl) (height br)
  end.

Definition t1 := bnode orb (bleaf true) (bnode andb (bleaf false) (bleaf true)).
Definition t2 := bnode orb (bnode andb (bleaf true) (bleaf false)) (bleaf true).

Eval compute in height t1.
Eval compute in height t2.

(* b *)

Fixpoint mirror (t:bTree) : bTree :=
  match t with
    | bleaf b => bleaf b
    | bnode o bl br => bnode o (mirror br) (mirror bl)
  end.

Eval simpl in mirror t1.
Eval simpl in mirror t2.

Print t1.
Print t2.

(* c *)

Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

Check hleaf true.
Check hnode 0 andb (hleaf true) (hleaf true).
Check hnode 1 andb (hnode 0 andb (hleaf true) (hleaf true)) (hnode 0 andb (hleaf true) (hleaf true)).

Fixpoint forgetful (n:nat) (t: hbTree n) : bTree :=
  match t with
    | hleaf b => bleaf b
    | hnode m o bl br => bnode o (forgetful m bl) (forgetful m br)
  end.

Eval compute in forgetful 0 (hleaf true).
Eval compute in forgetful 1 (hnode 0 andb (hleaf true) (hleaf true)).
Eval compute in forgetful 2 (hnode 1 andb (hnode 0 andb (hleaf true) (hleaf true)) (hnode 0 andb (hleaf true) (hleaf true))).
