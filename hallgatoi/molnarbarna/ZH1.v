  Structure GraphConst : Type := make_GraphConst
{
  G :> Set;

  E : G -> G -> Prop ;

  undirected : forall a b, E a b -> E b a;
  noloop : forall a, ~ (E a a);
}.

Print GraphConst.



Inductive csucsok:Set:=
  | x : csucsok
  | y : csucsok
  | z : csucsok.

Search Prop.

Definition huh (a:csucsok)(b:csucsok):Prop:=
  match a with 
  | x => True
  | y => True
  | z => True
  end.



Definition elek2 (a:csucsok)(b:csucsok):=
  match a, b with
  | x, y => huh x y
  | y, x => huh y x
  | y, z => huh y z
  | z, y => huh z y
  | x, x  => ~huh x x
  | x, z => ~ huh x z
  | y, y => ~huh y y
  | z, x => ~huh z x
  | z, z => ~huh z z
  end.

Definition elek (a:csucsok)(b:csucsok):Prop:=
  match a , b with
  | x, y => True
  | y, x => True
  | y, z => True
  | z, y => True
  | _, _  => False
  end.




Print E.

Definition sajat:GraphConst.
  apply (make_GraphConst csucsok elek2).
  induction a, b;compute;auto.
  induction a; compute; auto.
Defined.


Theorem sajatra: exists x y z: csucsok,((x<>y)/\ (y<>z) /\ (x<>z)) /\(~(elek x y) \/ ~(elek y z) \/ ~(elek x z)).
Proof.
  exists x.
  exists y.
  exists z.
  split.
  split.
  discriminate.
  split.
  discriminate.
  discriminate.
  compute;auto.
Qed.




Print sajat.
Eval compute in E sajat x z.

Theorem triangle_free : exists G : GraphConst, (exists x y z : G, ((x<>y)/\ (y<>z) /\ (x<>z))
/\ (~(E G x y) \/ ~(E G y z) \/ ~(E G x z))).
Proof.
  exists sajat.
  exists x.
  exists y.
  exists z.
  repeat split;auto.
  discriminate.
  discriminate.
  discriminate.
  right.
  right.
  compute.
  auto.  
Qed.


Inductive csucsok_tiz:Set:=
  | q : csucsok_tiz
  | w : csucsok_tiz
  | e : csucsok_tiz
  | r : csucsok_tiz
  | t : csucsok_tiz
  | m : csucsok_tiz
  | u : csucsok_tiz
  | i : csucsok_tiz
  | o : csucsok_tiz
  | p : csucsok_tiz.

Definition elek_tiz (a:csucsok_tiz)(b:csucsok_tiz):=
  match a, b with
  | q, q => False
  | w, w => False
  | e, e => False
  | r, r => False
  | t, t => False
  | m, m => False
  | u, u => False
  | i, i => False
  | o, o => False
  | p, p => False
  | _, _ => True
  end.

Definition teljes_tiz:GraphConst.
  apply (make_GraphConst csucsok_tiz elek_tiz).
  induction a, b; compute; auto.
  induction a; compute; auto.
Defined.

Theorem triangle_has : exists G : GraphConst, (exists x y z : G, ((x<>y)/\ (y<>z) /\ (x<>z))
/\ ((E G x y) /\ (E G y z) /\ (E G x z))).
Proof.
  exists teljes_tiz.
  exists q.
  exists w.
  exists e.
  repeat split;auto;discriminate.
Qed.
  
  

  