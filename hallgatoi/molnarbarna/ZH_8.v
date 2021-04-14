Require Import ZArith.
Definition szam (k:Z):Z:=
  k.


Print Z.


Eval compute in szam (Zneg 10).

Inductive Z_btree : Set :=
  | leaf : Z -> Z_btree
  | bnode : Z -> Z_btree-> Z_btree -> Z_btree.

Eval compute in szam 0.



Type (leaf 0).

Fixpoint vannulla(t:Z_btree):bool:=
  match t with
  | leaf 0=> true
  | leaf _=> false
  | bnode 0 t1 t2 => true
  | bnode _ t3 t4 => orb(vannulla(t3))(vannulla(t4))
  end.

Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base.
Local Open Scope Z_scope.
Notation dec_eq := Z.eq_decidable (only parsing).
Notation dec_Zle := Z.le_decidable (only parsing).
Notation dec_Zlt := Z.lt_decidable (only parsing).

Print Z.eqb.

Eval compute in Z.eqb (0)(0).




Eval compute in vannulla(bnode (-1) (leaf 10)(leaf (0))). 

Fixpoint vanbennek(t:Z_btree)(k:Z):bool:=
  match t with
  | leaf m=> Z.eqb(k)(m)
  | bnode u t1 t2 => match Z.eqb(k)(u) with
                       | true => true
                       | false => orb(vanbennek(t1)(k))(vanbennek(t2)(k))
                        end
  end.


Eval compute in vanbennek(bnode (-1) (leaf 10)(leaf (0)))(10). 
