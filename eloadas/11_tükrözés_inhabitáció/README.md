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
>(Γ : list Sent) ⊢ (A : Sent) 
relációt levezethetőségnek nevezzük.

_Levezetési szabályok:_

