# Fák

## Ismétlés, összefoglalás

A Coq nyelve egy függő típusos lamda kalkulusra épül. Ennek atomi típusai: ````Set, Prop, Type(i)````. A kifejezések közül az atomiak a változók. Az összetett típusokat vagy a *Pi* operátorral készítjük el vagy új típusokkal bővítjük a nyelvet, amiket *induktív* módon vezetünk be. A <img src="https://render.githubusercontent.com/render/math?math=%5CGamma"> *kontextus* egy <img src="https://render.githubusercontent.com/render/math?math=%5C%7Bx%3AA%2C%20y%3AB%2C%20%5Cdots%5C%7D"> alakú halmaz, ami változók deklarációit tartalmazza és lényegében a premisszák kerülnek bele. A <img src="https://render.githubusercontent.com/render/math?math=%5C%7Bx%3AA%2C%20y%3AB%2C%20%5Cdots%5C%7D%5Cvdash%20%3F%3AC"> feladat a Proof Mode-ban az ------------- jelnél tanultakhoz kapcsolódik:

````coq
x:A
y:B
...
-----------(1/1)
C
````
itt a feladat a C típus M lakójának megtalálása. Ha megtaláltuk M-et, akkor ennek típuselméleti írásmódja: <img src="https://render.githubusercontent.com/render/math?math=%5C%7Bx%3AA%2C%20y%3AB%2C%20%5Cdots%5C%7D%5Cvdash%20M%3AC">.

A Pi típusra vonatkozó jólformáltsági szabály: 

|Pi formációs szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%3AType%5Cquad%5Cquad%20%5CGamma%2Cx%3AA%5Cvdash%20B%3AType%7D%7B%5CGamma%5Cvdash%20%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%3AType%7D">
---------|-------

Az <img src="https://render.githubusercontent.com/render/math?math=%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B"> típus Coq-beli jelölése: 

````coq
forall x:A, B
````
jelentését a halmazelméletben a halmazok Descartes-szorzata adja. Ha <img src="https://render.githubusercontent.com/render/math?math=(B_x)_%7Bx%5Cin%20A%7D"> indexelt halmazcsalád, azaz egy olyan függvény, ami minden A-beli x-hez egy B_x halmazt rendel, akkor ennek a családnak a szorzata: 

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle%20%5Cprod_%7Bx%5Cin%20A%7DB_x%3D%5Cleft%5C%7Bf%3AA%5Cto%20B%5Cmid%20f(x)%5Cin%20B_x%5Cright%5C%7D">

Ennek elemei tehát pontosan azok a függvények, amik A-n értelmezettek és olyan az értékük, hogy minden x-re az A-ból, f(x) éppen B_x eleme. 

A Pi típus konstruktora a típuselméletben a lambda operátor:

 Pi bevezetési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%3AType%5Cquad%5Cquad%20%5CGamma%2Cx%3AA%5Cvdash%20M%3AB%7D%7B%5CGamma%5Cvdash%20%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%7D"> 
 -------|------

A Coq írásmódjában <img src="https://render.githubusercontent.com/render/math?math=%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B">:

````coq
fun x : A => M : 
                 forall x : A, B
````

Ennek a kostruktornak a destruktora az applikáció, vagy függvénykiszámítás:

Pi kiküszöbölési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20M%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%5Cquad%5Cquad%20%5CGamma%20%5Cvdash%20N%3AA%7D%7B%5CGamma%5Cvdash%20M%20N%20%3A%20B%5Bx%2FN%5D%20%7D">
----- | -----

Világos, hogy ha egy függvényt applikálunk egy az inputjával egyező típusú értékkel, akkor egy olyan kifejezést kapunk, ami kiszámításért kiált. Ez az érték a beta reduktum:

Pi komputációs szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%20%5Cquad%5Cquad%20%5CGamma%20%5Cvdash%20N%3AA%7D%7B%5CGamma%5Cvdash%20(%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM)%20N%20%5C%3B%5Cto_%5Cbeta%20%5C%3BM%5Bx%2FN%5D%3AB%5Bx%2FN%5D%20%7D"> 
-------|--------

## Természetes számok

Ez egy elég kemény dió. Sok csomag és taktika van, ami ezzel küzd: omega, crush, Mathematical Components.

````coq
SearchAbout plus.

Theorem n_plus_O : forall n : nat, n + O = n.
Proof. 
  intros.
  induction n.
  unfold plus.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Show Proof.
Qed.
````

## Fák, bokrok, ligetek

````coq
Inductive tree : Set :=
  | l : tree
  | n : tree -> tree -> tree.

Fixpoint length (t:tree) : nat :=
  match t with
    | l => 1
    | n t1 t2 => (length t1) + (length t2) end. 

Theorem levelhossz : length(l)=1.
Proof. 
  unfold length.
  reflexivity.
Qed.

Fixpoint right (t s : tree) : tree :=
  match t with
    | l => n l s
    | n t0 t1 => n t0 (right t1 s) end. 

Eval compute in right (n l l) (n l (n l l)).

Theorem ossz_tree : forall t s : tree, length (right t s) = length t + length s.
Proof.
  intros.
  induction t.
  simpl.
  reflexivity.
  simpl.
  rewrite IHt2.
  Require Import Omega.
  omega.
Qed.

Theorem ossz_tree_ll : length (right l l) = length l + length l.
Proof.
  apply ossz_tree with (t:=l) (s:=l).
Qed.
````

## Műveleket fákkal 

````coq(* Műveleti jelek halmazának definíciója*)

Inductive Operator : Set :=
  | Plus : Operator
  | Mult : Operator.

(*Absztrakt szintaxis fa definíciója
(leveleken számok, csúcsokban műveleti jelek).*)

Inductive AST : Set :=
  | leaf : nat -> AST
  | node : Operator -> AST -> AST -> AST.

(*Teszt arra, hogy ha pl. a (2*3)+6 -ot akarjuk szintaxisfaként kódolni,
akkor a kifejezés szándékolt kódja AST típusú lesz-e. *)

Check node Plus (node Mult (leaf 2) (leaf 3)) (leaf 6).

(*Kimenet:
node Plus (node Mult (leaf 2) (leaf 3)) (leaf 6)
     : AST
*)

(*Kiszámítási algoritmus. Rekurzív: alacsonyabb fákra meghívja magát.*)

Fixpoint evaluation (t : AST) : nat :=
  match t with
    | leaf l => l
    | node o t_1 t_2 => match o with
                          | Plus => plus (evaluation t_1) (evaluation t_2)
                          | Mult => mult (evaluation t_1) (evaluation t_2)
                        end
  end.

(*Teszt arra, hogy (2*3)+6=12 *)

Eval compute in evaluation (node Plus (node Mult (leaf 2) (leaf 3)) (leaf 6)).

(*Kimenet:
 = 12
     : nat
*)

(*De levelekkel is elbánik*)

Eval compute in evaluation (leaf 6).

(*Kimenet:
 = 6
     : nat
*)

(*Vegyük észre, hogy a fa minden elemét egyszer érinti az algoritmus!
Ezért ha a bemenet a szintaxisfa kódja és ennek hossza ''n'', akkor
a kimenet O(n) idejű. Az algoritmus tehát LINTIME-beli. *)
````

## Absztrakt szintaxis fák

````coq
(*Vegyük észre, hogy a fa minden elemét egyszer érinti az algoritmus!
Ezért ha a bemenet a szintaxisfa kódja és ennek hossza ''n'', akkor 
a kimenet O(n) idejű. Az algoritmus tehát LIN-beli. *)

(*Na, jó, de ez tök ugyanaz, mint az andb :D *)

(* A Coq egyik feladata a szintaxis kezelése *)

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


(*Absztrakt szintaxis fa definíciója

BinAST {Atom:Set} {Operator:Set}

 *)

Check anode Plus (aleaf (At 3)) (aleaf (At 4)).

(*Modell definíciója*)

Structure Model : Type := const_kozos
{
  A :> Set;

  op1 : A -> A -> A ;
  op2 : A -> A -> A ;
}.

(*Értékelés definíciója: v: Atom -> M, ahol M : Model *)

(*Összetett kifejezés értékelése*)

(*Kiszámítási algoritmus. Rekurzív: alacsonyabb fákra meghívja magát.*) 

Fixpoint eval (M:Model) (v:Atom -> M) (t : BinAST) : M :=
  match t with 
    | aleaf l => v(l)
    | anode o t_1 t_2 => match o with 
                          | Plus => op1 M (eval M v t_1) (eval M v t_2)
                          | Mult => op2 M (eval M v t_1) (eval M v t_2)
                        end
  end.

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


(*Vegyük észre, hogy a fa minden elemét egyszer érinti az algoritmus!
Ezért ha a bemenet a szintaxisfa kódja és ennek hossza ''n'', akkor 
a kimenet O(n) idejű. Az algoritmus tehát LIN-beli. *)
````


