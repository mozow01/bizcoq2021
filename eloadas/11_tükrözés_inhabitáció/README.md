# Természetes levezetés

Az intuicionista propozicionális logika bevezetési és kiküszöbölési szabályokra épülő levezetési rendszere (természetes levezetés) az **Ni** kódú logika. Ez része a Coq-nak, mint alap kiterjesztés, de modellezhető is benne. Ezt hívjuk reflection-nek.

_Nyelv:_

````coq
Inductive Sent : Set :=
  | At : nat -> Sent
  | Impl : Sent -> Sent -> Sent
  | Conj : Sent -> Sent -> Sent 
  | Disj : Sent -> Sent -> Sent
  | Fals : Sent.  

Notation "A → B" := (Impl A B) (at level 20, right associativity) : type_scope.
Notation "A ∧ B" := (Conj A B) (at level 20) : type_scope.
Notation "A ∨ B" := (Disj A B) (at level 20) : type_scope.
Notation "⊥" := Fals (at level 20) : type_scope.
````

Kontextus (premisszahalmaz) és kétardumentumú levezethetőség reláció:

````coq
Judgement : list Sent -> Sent -> Prop
````

ahol Γ : list Sent -eket kontextusnak. Judgement : list Sent -> Sent -> Prop vagy röviden a 
> Γ ⊢ A  

relációt levezethetőségnek nevezzük.

_Levezetési szabályok:_

**Var**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%20%5Cquad%5Cquad%20%7D%7B%5CGamma%5Cvdash%20A%7D%5Cquad%5Cquad%5Cquad%5Cquad%20(A%5Cin%20%5CGamma)">

**Ded** és **Mp**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%5BA%5D%5C%5C%5Cvdots%5C%5C%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20%20B%5Cend%7Bmatrix%7D%20%7D%7B%5CGamma%5Cvdash%20A%5Cto%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%20%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cto%20B%20%5Cquad%5Cquad%20%5CGamma%5Cvdash%20A%7D%7B%5CGamma%5Cvdash%20B%7D">

**AndIntro** és **AndInd**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cquad%5Cquad%5CGamma%5Cvdash%20B%7D%7B%5CGamma%5Cvdash%20A%5Cwedge%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%20%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%26%20%5CGamma%5Ccup%5C%7BA%2C%20B%5C%7D%5Cvdash%20%5BA%5D%2C%5BB%5D%20%5C%5C%20%26%20%5Cvdots%20%5C%5C%5CGamma%5Cvdash%20A%5Cwedge%20B%5Cquad%5Cquad%20%26%20%5CGamma%5Ccup%5C%7BA%2C%20B%5C%7D%5Cvdash%20C%20%5Cend%7Bmatrix%7D%7D%7B%5CGamma%5Cvdash%20C%7D">

**OrIntro** és **OrInd**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%7D%7B%5CGamma%5Cvdash%20A%5Cvee%20B%7D%5Cquad%5Cdfrac%7B%5CGamma%5Cvdash%20B%7D%7B%5CGamma%5Cvdash%20A%5Cvee%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%26%20%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20%5BA%5D%20%26%20%5CGamma%5Ccup%5C%7BB%5C%7D%5Cvdash%20%5BB%5D%20%5C%5C%20%26%20%5Cvdots%20%26%20%5Cvdots%20%5C%5C%0A%5CGamma%5Cvdash%20A%5Cvee%20B%5Cquad%5Cquad%20%26%20%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20C%20%26%20%5CGamma%5Ccup%5C%7BB%5C%7D%5Cvdash%20C%20%5Cend%7Bmatrix%7D%7D%7B%5CGamma%5Cvdash%20C%7D">

**Abs**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%5Cbot%7D%7B%5CGamma%5Cvdash%20A%7D">

Implementáció:

````coq
Reserved Notation "Γ ⊢ A" (at level 99).
Inductive Judgement : list Sent -> Sent -> Prop :=
| Var    : forall Γ A, In A Γ -> Γ ⊢ A
| ImplI  : forall Γ A B, A::Γ ⊢ B -> Γ ⊢ A → B
| ImplE  : forall Γ A B, Γ ⊢ A → B -> Γ ⊢ A -> Γ ⊢ B
| ConjI  : forall Γ A B, Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A ∧ B
| ConjE  : forall Γ A B C, Γ ⊢ A ∧ B -> B::A::Γ ⊢ C -> Γ ⊢ C
| DisjI1 : forall Γ A B, Γ ⊢ A -> Γ ⊢ A ∨ B
| DisjI2 : forall Γ A B, Γ ⊢ B -> Γ ⊢ A ∨ B
| DisjE  : forall Γ A B C, Γ ⊢ A ∨ B -> A::Γ ⊢ C -> B::Γ ⊢ C -> Γ ⊢ C
| FalsI  : forall Γ A, Γ ⊢ ⊥ -> Γ ⊢ A
where "Γ ⊢ A" := (Judgement Γ A) : type_scope.
````

## Reprezentáció

A változóértékelések típusa a ````VAL := nat -> Prop```` függvényt.

A mondatfordítás egy ````VAL' : VAL -> Sent -> Prop```` függvény, ami kirejeszti VAL-t rekurzívan Sent-re.

Ítéletfordítás egy ````VAL'' : VAL' -> list Sent -> Prop```` függvény, ami az Γ ⊢ A alakú tárgynyelvi kifejezéseket fordítja le a Coq home-nyelvére.

_Soundness:_ ````forall Γ A v, Γ ⊢ A -> VAL'' v Γ A````

(ez nehéz!)

Általában bizonytalan a _Completeness:_ ````forall Γ A, (forall v, VAL'' v Γ A ) -> Γ ⊢ A````.

## Inhabitációs algoritmus

[Innen](https://github.com/mozow01/bizcoq2021/blob/main/forrasok/typ_alg.pdf)

## Házi feladatok

**1.** Tekintsük az alábbi, Arthur Priortól származó levezetési rendszert, amiben A tonk B az egyetlen mondatkonnektívum.

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BA%5Cin%20%5CGamma%7D%7B%5CGamma%20%5Cvdash%20A%7D%2C%5Cquad%20%0A%5Cdfrac%7BA%5C%3B%5Cmathrm%7Btonk%7D%5C%3BB%7D%7BA%7D%2C%20%5Cquad%20%0A%5Cdfrac%7BA%5C%3B%5Cmathrm%7Btonk%7D%5C%3BB%7D%7BB%7D%2C%20%5Cquad%0A%5Cdfrac%7BA%7D%7BA%5C%3B%5Cmathrm%7Btonk%7D%5C%3BB%7D%2C%20%5Cquad%0A%5Cdfrac%7BB%7D%7BA%5C%3B%5Cmathrm%7Btonk%7D%5C%3BB%7D">

Implementáljuk ezt a rendszert Coq-ban, ahogy azt a Ni-vel tettük fent, és igazoljuk, hogy: 

````coq
Theorem tonk_problem : forall A B Γ, In A Γ -> Γ ⊢ B.
````

vagyis, hogy ez a rendszer teljességgel hasznavehetetlen :)

(Priornál ez arra volt példa, hogy nem lehet akárhogyan megválogatni a bevezetési és kiküszöbölési szabályokat -- persze csak arról van szó, hogy meg lehet választani akárhogyan, legfeljebb triviális lesz a rendszer.)

**2.** Emlékezzünk vissza erre az algoritmusra:

````coq
Inductive Operator : Set :=
  | Plus : Operator
  | Mult : Operator.

Inductive AST : Set :=
  | leaf : nat -> AST
  | node : Operator -> AST -> AST -> AST.

Fixpoint evaluation (t : AST) : nat :=
  match t with
    | leaf l' => l'
    | node o t_1 t_2 => match o with
                          | Plus => plus (evaluation t_1) (evaluation t_2)
                          | Mult => mult (evaluation t_1) (evaluation t_2)
                        end
  end.
````

Milyen bonyolultsági osztályba sorolható az algoritmus, amennyiben DTM-ként ill. ATM-ként gondolunk rá? (Tehát PTIME, LOGTIME, EXPTIME, APTIME, ALOGTIME, AEXPTIME?) Azt is adjuk meg, hogy mi az input mérete, amiben a futási időt mérjük! (Emlékeztető: az ATM párhuzamos műveleteket is tud végrezni és a párhuzamosan végzett rekurzív hívások közül csak a leghosszab számítási út számít, de nem az összes hívás. A DTM-ben minden művelet számít.)
