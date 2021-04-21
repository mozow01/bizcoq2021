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

**Var** szabály

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%20%5Cquad%5Cquad%20%7D%7B%5CGamma%5Cvdash%20A%7D%5Cquad%5Cquad%5Cquad%5Cquad%20(A%5Cin%20%5CGamma)">

**Ded** és **Mp**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%5BA%5D%5C%5C%5Cvdots%5C%5C%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20%20B%5Cend%7Bmatrix%7D%20%7D%7B%5CGamma%5Cvdash%20A%5Cto%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%20%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cto%20B%20%5Cquad%5Cquad%20%5CGamma%5Cvdash%20A%7D%7B%5CGamma%5Cvdash%20B%7D">

**AndIntro** és **AndInd**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cquad%5Cquad%5CGamma%5Cvdash%20B%7D%7B%5CGamma%5Cvdash%20A%5Cwedge%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%20%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%26%20%5CGamma%5Ccup%5C%7BA%2C%20B%5C%7D%5Cvdash%20%5BA%5D%2C%5BB%5D%20%5C%5C%20%26%20%5Cvdots%20%5C%5C%5CGamma%5Cvdash%20A%5Cwedge%20B%5Cquad%5Cquad%20%26%20%5CGamma%5Ccup%5C%7BA%2C%20B%5C%7D%5Cvdash%20C%20%5Cend%7Bmatrix%7D%7D%7B%5CGamma%5Cvdash%20C%7D">

**OrIntro** és **OrInd**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%7D%7B%5CGamma%5Cvdash%20A%5Cvee%20B%7D%5Cquad%5Cdfrac%7B%5CGamma%5Cvdash%20B%7D%7B%5CGamma%5Cvdash%20A%5Cvee%20B%7D%5Cquad%5Cquad%5Cquad%5Cquad%20%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%26%20%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20%5BA%5D%20%26%20%5CGamma%5Ccup%5C%7BB%5C%7D%5Cvdash%20%5BB%5D%20%5C%5C%20%26%20%5Cvdots%20%26%20%5Cvdots%20%5C%5C%0A%5CGamma%5Cvdash%20A%5Cvee%20B%5Cquad%5Cquad%20%26%20%5CGamma%5Ccup%5C%7BA%5C%7D%5Cvdash%20C%20%26%20%5CGamma%5Ccup%5C%7BB%5C%7D%5Cvdash%20C%20%5Cend%7Bmatrix%7D%7D%7B%5CGamma%5Cvdash%20C%7D">

**Abs**

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%5Cbot%7D%7B%5CGamma%5Cvdash%20A%7D">

