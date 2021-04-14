Structure GraphClassical : Type := make_GraphClassical
{
  G' :> Set;

  E' : G' -> G' -> bool ;

  undirected' : forall a b, implb (E' a b) (E' b a) = true;
  noloop' : forall a, negb (E' a a) = true;
}.


Structure Graph : Type := make_Graph
{
  G'' :> Set;

  E'' : G'' -> G'' -> bool ;

  undirected'' : forall a b, implb (E'' a b) (E'' b a) = true;

}.


Search bool.

Inductive csucsok1:Set:=
  | x :csucsok1
  | y :csucsok1.

Definition elek1(a:csucsok1)(b:csucsok1):=
  match a, b with
    | x, y => true
    | y, x => true
    | _, _ => false 
    end.

Definition elso:GraphClassical.
  apply(make_GraphClassical csucsok1 elek1).
  induction a,b;auto.
  induction a;auto.
Defined.

Search bool.
Print eq_true.


Search Set.

Search bool.

Definition kompl (G:GraphClassical):G -> G -> bool:=
fun a b =>negb(E' G a b).

Definition kompl2 (G:GraphClassical):G -> G -> bool:=
fun a b =>negb(E' G b b).




Eval compute in kompl elso y y.
  

Theorem law_of_contradiction : forall (P Q : Prop),
  P /\ ~P -> Q.
Proof.
  intros P Q P_and_not_P.
  destruct P_and_not_P as [P_holds not_P].
  contradiction.
Qed.

Search bool.

Theorem egyenlo(a:bool)(b:bool): ((implb(a)(b)=true) /\ (implb(b)(a))=true)-> a=b.
  intros.
  induction a,b;auto.  
  destruct H.
  discriminate.
  destruct H.
  discriminate.
Qed.



Theorem elekodavissza: forall (G1:GraphClassical),forall a b:G1, E' G1 a b = E' G1 b a.
  intros.
  enough (implb (E' G1 a b) (E' G1 b a) = true).
  enough (implb (E' G1 b a) (E' G1 a b) = true).
  apply (egyenlo (E' G1 a b)(E' G1 b a)).
  compute;auto.
  rewrite undirected'.
  auto.
  rewrite undirected'.
  auto.
Defined.

Definition komplementer (G1: GraphClassical):Graph.
  apply (make_Graph (G' G1) (kompl G1)).
  intros.
  unfold kompl.
  enough (((E' G1 a b))=((E' G1 b a))).
  rewrite H. 
  induction (E' G1 b a).
  compute;auto.
  compute;auto.
  rewrite elekodavissza.
  auto.
Defined.


Definition masodikel(a:csucsok1)(b:csucsok1):=
  match a, b with
    | x, y => false
    | y, x => false
    | _, _ => true 
    end.

Definition masodik:Graph.
  apply (make_Graph csucsok1 masodikel).
  induction a,b;auto.
Defined.
  
Type E'' masodik.


Definition komplementere (G1:GraphClassical)(G2:Graph):Prop:=
  (komplementer G1) = G2.






Theorem proba2: komplementere elso masodik.
  unfold komplementere.
  unfold komplementer.
  unfold masodik.
  unfold elso.
  compute;auto.
  induction a,b:csucsok1.
Qed.



  
  




