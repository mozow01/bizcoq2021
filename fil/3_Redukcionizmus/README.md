# Reduktív osztály, vitatott osztály

## Dummett redukcionizmusa

Dummett a tudományokat úgy osztályozta, hogy meghatározott mondatoknak két körét. Az első a _reduktív osztály,_ amelyben a mondatok igazsága problémamentes, a második a _vitatott osztály,_ amelyben a mondatok érvényességét a reduktív osztály érvényességéból nyerik. Ez a matematikában Hilbert finitista-konvencionalista megoldása. 

Vitatott például a **kizárt harmadik elve**: "A vagy nem A". A Coq logikájában ez nem általános igazság.

````coq
Require Import Arith.

Fixpoint nat_egyenlő (n m : nat) : Prop :=
match n, m with 
  | 0, 0 => True
  | S n', 0 => False
  | 0, S m' => False
  | S n', S m' => nat_egyenlő n' m' 
end.

Print Nat.eq_dec.
````

## Konstruktív logika

Ebben a logikában a levezetési szabályok vezetik az érveléseket: egy összetett kifejezés csak a fő konnektívumra csak bevezetési szabálya alkalmazásával következtethetünk.

````coq
Theorem problem_1 : forall A B : Prop, (A -> B) -> (~ A \/ B).
Proof.
intros.
left.
Admitted.


Theorem problem_2 : forall A B : Prop, (~ A \/ B) -> (A -> B).
Proof.
intros.
destruct H as [H1|H2].
contradiction.
auto.
Qed.
```

