# Fák, listák 2.

## Paralell programvégrehajtás, tree as a program.

````coq
Inductive At : Set :=
  | At_c : nat -> At.

Inductive UnOp : Set :=
  | NOT : UnOp.

Inductive BinOp : Set :=
  | AND : BinOp
  | OR : BinOp.

Inductive Exp : Set :=
  | const : At -> Exp
  | NOT_c : Exp -> Exp
  | AND_c : Exp -> Exp -> Exp
  | OR_c : Exp -> Exp -> Exp.

Inductive AST : Set :=
  | leaf : At -> AST 
  | node1 : UnOp -> AST -> AST
  | node2 : BinOp -> AST -> AST -> AST.

Fixpoint ExpDenote (e:Exp) (v : nat -> bool) : bool :=
match e with 
  | const (At_c n) => v n
  | NOT_c e1 => negb (ExpDenote e1 v)
  | AND_c e1 e2 => andb (ExpDenote e1 v) (ExpDenote e2 v)
  | OR_c e1 e2 => orb (ExpDenote e1 v) (ExpDenote e2 v)
end.

Fixpoint ASTEval (t : AST) (v : nat -> bool) {struct t} : bool :=
match t with 
  | leaf (At_c n) => v n
  | node1 _ t1 => negb (ASTEval t1 v)
  | node2 x t1 t2 => 
match x with
  | AND => andb (ASTEval t1 v) (ASTEval t2 v)
  | OR => orb (ASTEval t1 v) (ASTEval t2 v)
end
end.

Fixpoint Translation_1 (t : AST) :=
match t with
  | leaf (At_c n) => const (At_c n)
  | node1 _ t1 => NOT_c (Translation_1 t1)
  | node2 x t1 t2 => 
match x with
  | AND => AND_c (Translation_1 t1) (Translation_1 t2)
  | OR => OR_c (Translation_1 t1) (Translation_1 t2)
end
end. 

Fixpoint Translation_2 (e : Exp) :=
match e with 
  | const (At_c n) => leaf (At_c n)
  | NOT_c e1 => node1 NOT (Translation_2 e1)
  | AND_c e1 e2 => node2 AND (Translation_2 e1) (Translation_2 e2)
  | OR_c e1 e2 => node2 OR (Translation_2 e1) (Translation_2 e2)
end.

Theorem Soundness_1 : forall (e : Exp) (v  : nat -> bool), 
ExpDenote e v = ASTEval (Translation_2 e) v.
Proof.
intros.
induction e.
induction a.
compute.
reflexivity.
simpl.
rewrite IHe.
auto.
Admitted.

Qed.
````

## Két kétváltozós művelet kiértékelése absztrakt környezetben

Az előző órán egy ,,konkrét'' absztrakt szintaxis fát értékeltünk ki, ahol az AST levelein bool kifejezések voltak, csúcsaiban bool műveletek. Most mindent paraméteresen veszünk föl. Lesz egy fák formájában kódolt nyelv és lesz a valóság, amiről ez a nyelv beszél. 

|Nyelv|Valóság|
|--- |----|
|<img src="https://github.com/mozow01/bizcoq2021/blob/main/forrasok/robot-toy-technology-electronics-cat-25-512.svg"  width="100" >|<img src="https://github.com/mozow01/bizcoq2021/blob/main/forrasok/gLiom501.svg"  width="100" >|

Először is a ,,nyelv''.

````coq
Inductive BinAST {A:Set} {O:Set} : Type :=
  | aleaf : A -> BinAST
  | anode : O -> BinAST -> BinAST -> BinAST.

(* Elemnevek halmazának definíciója*)

Inductive Atom :  Set :=
  | At : nat -> Atom.

Check At(3).

(* Műveleti jelek halmazának definíciója*)

Inductive Operator : Set :=
  | Plus : Operator
  | Mult : Operator.

Check anode Plus (aleaf (At 3)) (aleaf (At 4)).

````
Ennek a nyelvnek ( ~(=^..^) ) sok modellje ( :scream_cat: ) lehet. Most azt a struktúratípust definiáljuk, amiről szándékoztunk volna a fentiekben a beszélni.

````coq
Structure Model : Type := const_kozos
{
  A :> Set;

  op1 : A -> A -> A ;
  op2 : A -> A -> A ;
}.

(*Értékelés definíciója: v: Atom -> M, ahol M : Model *)
````

Teljesen mindegy azonban mi a modell, a kiértékelés ugyanúgy megy:

````coq
Fixpoint eval (M:Model) (v:Atom -> M) (t : BinAST) : M :=
  match t with 
    | aleaf l => v(l)
    | anode o t_1 t_2 => match o with 
                          | Plus => op1 M (eval M v t_1) (eval M v t_2)
                          | Mult => op2 M (eval M v t_1) (eval M v t_2)
                        end
  end.
````

ahol v adja meg az atomok konkrét értékét az M modellben. Például maga ````nat```` az összeadással és szorzással is modell: 

````coq
Definition NAT_Model : Model := const_kozos nat plus mult.


Definition v: Atom -> nat := fun x => match x with 
                                        | At 0 => 2
                                        | At 1 => 3
                                        | At 2 => 6
                                        | _ => 0
                                      end.


(*Teszt arra, hogy (2*3)+6=12 *)

Eval compute in eval NAT_Model v 
(anode Plus (anode Mult (aleaf (At 0)) (aleaf (At 1))) (aleaf (At 2))).

(*Kimenet: 
 = 12
     : nat
*)

Theorem test : eval NAT_Model v 
(anode Plus (anode Mult (aleaf (At 0)) (aleaf (At 1))) (aleaf (At 2)))=12.
Proof. 
  simpl. auto.
Qed.
````

## Egy ,,One-Shot DETERMINISTIC Decision Problem'' 

Kajálni szeretnénk ,,pizzáért indultam, de giros lett belőle'' szellemben. A vállalkozók áldozatai vagyunk. Hogy mit sikerül kapnunk, azt teljes egészében ők határozzák meg. 

<img src="https://render.githubusercontent.com/render/math?math=%5Cboxed%7Bs%3A%5Cmathrm%7BState%7D%7D%5C%3B%5C%3B%5Cxrightarrow%7Ba%3A%5Cmathrm%7BAction%7D%7D%5C%3B%5C%3B%20%5Cboxed%7Bs'%3A%5Cmathrm%7BState%7D%7D">

Ennek ellenére megpróbálunk racionális döntést hozni, melyben az is szerepet játszik, hogy milyen korábbi tapasztalataink vannak. A számunkra kedvező eseteket bónuszponttal jutalmazni fogjuk. (Úgy is fogalmazhatunk, kognitív tudományi szempontból, hogy megpróbáljuk kideríteni, hogy az agy ezt gyorsan dönti-e el: ha triviális a választás, akkor igen, ha nem, akkor nem.

Az állapotok a kaják lesznek: State = {pizza, bécsi, giros}, a tettek, hogy melyik kajáldába megyünk: Action = {Carlo, Margo, Artak}. Az átmenetfüggvény határozza meg, hogy mi, akik introvertáltak vagyunk, és az *s* kaját akarjuk és az *a* kajáldát választjuk, akkor milyen kaját kapunk ott. 

````transition (s:State) (a:Action) : State :=````

| |Carlo|Margo|Artak|
|---|---|---|---|
|pizza| pizza | pizza | giros|
|bécsi| pizza | bécsi | bécsi|
|giros| pizza | pizza | giros|

Preferenciáink is vannak: pl. tudjuk, hogy Margó baromi jó rántotthúst süt, de rossz pizzát és nem veszi föl a maszkot, mert vírustagadó. A többi árús kb. OK. Ezt a juti függvény adja meg:

````utility (s:State) (a:Action) : nat :=````

| |Carlo|Margo|Artak|
|---|---|---|---|
|pizza| 9 | 2 | 0 |
|bécsi| 0 | 10 | 7 |
|giros| 0 | 0 | 10|

A *modell* szerint úgy döntük, hogy készítünk egy ágens ( :trollface: ) döntési függvényt, amit a következő optimalizációs számítást végzi el:

<img src="https://render.githubusercontent.com/render/math?math=%5Cmathrm%7BAgentAction%7D(s)%3D%5Cunderset%7Ba%3A%5Cmathrm%7BAction%7D%7D%7B%5Cmathrm%7Bargmax%7D%7D%5Cmathrm%7Butility%7D(%5Cmathrm%7Btransition(s%2Ca)%2Ca%7D)">

vagyis megmondja, mi az *s* kaja függvényében egy olyan *a* tett, amelyhez a legtöbb jutalompont tartozik. 

## Az ArgMax megvalósítása két lépésben -- pár vs lista, konkrét eset

````coq
Inductive H : Set :=
  | Carlo : H
  | Margo : H
  | Artak : H.

Print pair.

Require Import Omega List.

Definition MaxPairTwo (x y : H*nat) : H*nat :=
  match x, y with
    | pair a n, pair b m => 
       if (le_lt_dec m n) then pair a n else pair b m
  end.

Eval compute in MaxPairTwo (Margo,7) (Carlo,6).

Definition ArgMaxTwo (x y : H*nat) : H := fst(MaxPairTwo x y).

Eval compute in ArgMaxTwo (Margo,7) (Artak,6).

Definition MaxPairThree (x y z : H*nat) : H*nat := 
  MaxPairTwo (MaxPairTwo x y) z.

Eval compute in MaxPairThree (Margo,7) (Carlo,6) (Artak, 8).

Fixpoint MaxPair (l : list (H*nat)) : H*nat := 
  match l with 
   | nil => (Margo,0)
   | cons x l' => MaxPairTwo x (MaxPair l')
  end.

Eval compute in 
MaxPair ((Margo,7)::(Margo,8)::(Artak,6)::(Carlo,10)::nil).

(*A véges halmazon függvény, mint lista *)

Definition listing (f: H -> nat) : list (H*nat) := 
  (Carlo,f(Carlo))::(Margo,f(Margo))::(Artak,f(Artak))::nil. 

Definition f (x:H) : nat :=
  match x with
    | Carlo => 0
    | Margo => 2
    | Artak => 2
  end.

Eval compute in MaxPair (listing f).

Eval compute in fst (MaxPair (listing f)).
````

## Az ArgMax megvalósítása két lépésben -- opcionális típus, általános eset

````coq
Require Import Omega List.

Definition MaxPairTwo {X:Set} (x y : option (X*nat)) : option (X*nat) :=
  match x, y with
    | None, None => None
    | None, Some b => Some b
    | Some a, None => Some a
    | Some (pair a n), Some (pair b m) => 
       if (le_lt_dec m n) then Some (pair a n) else Some (pair b m)
  end.

Fixpoint MaxPair {X:Set} (l : list (option(X*nat))) : option (X*nat) := 
  match l with 
   | nil => None
   | cons x l' => MaxPairTwo x (MaxPair l')
  end.

Fixpoint MaxPair' (l : list (H*nat)) : option (H*nat) := 
  match l with 
   | nil => None
   | cons x l' => match (MaxPair' l') with 
                   | None => None
                   | Some c => Some (MaxPairTwo x c)
                  end
  end.
````
## A probléma megoldása

(folyt.)

````coq
Inductive Action : Set :=
  | Margo : Action
  | Carlo : Action
  | Artak : Action.

Inductive State : Set :=
  | pizza : State
  | bécsi : State
  | giros : State.

Definition transition (s:State) (a:Action) : State :=
  match s, a with
   | _ , Carlo => pizza
   | pizza , Margo => pizza
   | bécsi , Margo => bécsi   
   | _ , Margo => pizza
   | bécsi , Artak => bécsi
   | giros , Artak => giros
   | _ , Artak => giros
  end.

Eval compute in (transition pizza Artak).

Definition utility (s:State) (a:Action) : nat :=
  match s, a with
   | pizza , Carlo => 9
   | bécsi , Artak => 6
   | bécsi , Margo => 10
   | pizza , Margo => 2
   | giros , Artak => 10
   | _ , Margo => 0
   | _ , Carlo => 0
   | _ , Artak => 0
  end.

Definition listing (f: Action -> nat) : list (option(Action*nat)) := 
  Some (Carlo,f(Carlo))::Some (Margo,f(Margo))::Some (Artak,f(Artak))::nil. 

(*AgentAction(s) := arg max_a {utility(transition(s a) a)} *)

Definition AgentAction(s:State) : option Action := 
  ArgMax (listing (fun x:Action => utility (transition s x) x) ).

Eval compute in AgentAction pizza.
````
