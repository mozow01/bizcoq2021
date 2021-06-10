# Kifejezőképesség próbája

Az automatikus bizonyításellenőrző programok egyik szokásos tesztje az úgy nevezett Drinker's Paradox. Ez a következő:

<img src="https://render.githubusercontent.com/render/math?math=%5Cvdash_%7BCL%7D(%5Cexists%20%5C!x)(((%5Cexists%20%5C!%20x)A(x))%5Cto%20A(x))">

Vagyis van olyan, aki ha bárki iszik, ő is iszik. A duálisa: 

<img src="https://render.githubusercontent.com/render/math?math=%5Cvdash_%7BCL%7D(%5Cexists%20%5C!%20x)(A(x)%5Cto(%5Cforall%5C!%20x)A(x))">

azaz, van olyan, aki ha iszik, mindenki iszik. Ezek a klasszikus logika paradoxonai, azaz nem ellentmondások, csak furcsák. Hogy mi bennük a furcsa, az majd a bizonyításukból, ill. a BHK-interpretációbeli cáfolatukból fog kiderülni.

**Informális levezetés a klasszikus logikában.** Két eset van. Vagy igaz (∃x)A(x) vagy hamis. Ha igaz, akkor vehetünk egy olyan _a_ dolgot, amire igaz A(_a_). Mivel igazból következik az igaz, így ((∃x)A(x)) → A(_a_) igaz, hogy (∃x)(((∃x)A(x)) → A(x)). Ha (∃x)A(x) hamis, akkor bármilyen _a_-ra ((∃x)A(x)) → A(_a_), mert hamisból minden következik.

**BHK-cáfolat** Ha lenne (∃x)(((∃x)A(x)) → A(x))-nak konstruktív levezetése, akkor lenne _a_, hogy ((∃x)A(x)) → A(_a_). Ez az _a_ viszont független kell, hogy legyen A-tól, mert nem feltételezhetjük, hogy (∃x)A(x)-nak van igazságértéke.  

## Konstruktív próbálkozások

````coq
Print sig.

Print sum.

Inductive inhabited' (A : Type) : Type :=  inhabits' : A -> inhabited' A.

Print inhabited'_ind.

Parameter V : Set.

Parameter A' : V -> Prop.

Axiom LEM' : { x | A' x } + ({ x | A' x } -> False).

Axiom V_non_empty : inhabited' V.

Theorem Drinker's : { x | { x | A' x } -> A' x }.
Proof.
  assert (K := LEM').
  destruct K as [K1|K2].
  - apply exist  with (x:=(proj1_sig K1)).
  intros.
  exact (proj2_sig K1).
  - assert (L:=V_non_empty).
  elim L.
  intro x0.
  apply exist with (x:=x0).
  tauto.
  Show Proof.
Qed.
  
Print sig.

Print ex.

Definition ex_proj1 {A:Type} {P:A->Prop} (x : ex P) : A :=
    match x with ex_intro _ a _ => a end.

Definition ex_proj2 {A:Prop} {P:A->Prop} (x:ex P) : 
P (ex_proj1 x) :=
    match x with ex_intro _ _ b => b end.

Parameter U : Prop.

Parameter A : U -> Prop.

Definition LEM_form := (exists x, A x) \/ ~ (exists x, A x).

Axiom LEM : LEM_form.

Axiom U_non_empty : inhabited U. 

Theorem drinker's : exists x, (exists x, A x) -> A x.
Proof.
  assert (K := LEM).
  destruct K as [K1|K2].
  - apply ex_intro with (x:=(ex_proj1 K1)).
  intros.
  exact (ex_proj2 K1).
  - assert (L:=U_non_empty).
  elim L.
  intro x0.
  apply ex_intro with (x:=x0).
  tauto.
  Show Proof.
Qed.

Print inhabited. 
````

## Klasszikus logikai

````coq
Print ex_ind.

Parameter U : Set.

Parameter A : U -> Prop.

Definition LEM_form := (exists x, A x) \/ ~ (exists x, A x).

Axiom LEM : LEM_form.

Axiom U_non_empty : inhabited U.

Theorem drinker's : exists x, (exists x, A x) -> A x.
Proof.
  assert (K := LEM).
  destruct K as [K1|K2].
  firstorder.
  assert (L:=U_non_empty).
  firstorder.
Qed.

Theorem drinker's_1 : exists x, (exists x, A x) -> A x.
Proof.
  assert (K := LEM).
  destruct K as [K1|K2].
  Print ex_ind.
  - induction K1. 
  (* apply ex_ind with (A:=U) (P:=fun x => A x) 
     (P0:=exists x : U, (exists x0 : U, A x0) -> A x). 
  intros. *)
  apply ex_intro with (x:=x).
  all: auto.
  - assert (L:=U_non_empty).
  elim L.
  intro x0.
  apply ex_intro with (x:=x0).
  intro.
  contradiction.
  Show Proof.
Qed.
````
