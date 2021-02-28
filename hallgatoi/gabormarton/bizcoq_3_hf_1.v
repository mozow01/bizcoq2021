Inductive UBTree : Set :=
  | leaf0 : UBTree
  | node2 : UBTree -> UBTree -> UBTree
  | node1 : UBTree -> UBTree.

Fixpoint right_UB (t:UBTree) (s:UBTree) : UBTree :=
  match t with
    | leaf0 => node2 leaf0 s
    | node2 t0 t1 => node2 t0 (right_UB t1 s)
    | node1 t => node1 (right_UB t s)
  end. 

Eval compute in right_UB (node2 leaf0 leaf0) (node2 leaf0 (node2 leaf0 leaf0)).
Eval compute in right_UB (node2 leaf0 (node1 leaf0)) (node2 leaf0 (node2 leaf0 leaf0)).

(*

c) Definiáljuk UBTree-ben is a length_UB levélhossz függvényt és igazoljuk, hogy

forall s t : UBTree, length_UB(right_UB s t) =  length_UB s + length_UB t.
*)