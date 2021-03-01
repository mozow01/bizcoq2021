# Fák, listák 2.

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

