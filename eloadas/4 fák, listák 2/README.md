# Fák, listák 2.

## Két kétváltozós művelet kiértékelése absztrakt környezetben

Az előző órán egy ,,konkrét'' absztrakt szintaxis fát értékeltünk ki, ahol az AST levelein bool kifejezések voltak, csúcsaiban bool műveletek. Most mindent paraméteresen veszünk föl. Lesz egy fák formájában kódolt nyelv és lesz ennek a valóság, amiről ez a nyelv beszél. 

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
Ennek a nyelvnek sok modellje lehet. Most azt a struktúratípust definiáljuk, amiről szándékoztunk volna a fentiekben a beszélni.
