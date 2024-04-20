#  A filozófia csodálatos hatékonysága az automatikus tételbizonyításban
Molnár Zoltán Gábor, Algebra Tsz.

## Coq automatikus bizonyító és bizonyításmenedzselő program

Thierry Coquand, Christine Paulin-Mohring implementálták számítógépesen az _Induktív Konstrukciók Kalkulusát_ (CIC, CoC, Coq), ami Peer Martin-Löf típuselméletének átdolgozása. 

## Mi az az induktív adattípus?

"Szemléletesen, egy induktívan definiált típus konstruktorok egy teljes listája által adott. A nekik megfelelő indukciós elvvel érvelünk a típus elemeivel kapcsolatban és a konstruktorokon függvényeket adunk meg, amik alkamasak az egész típus felett értelmezett primitív rekurzív függvények definiálására." (Christine Paulin-Mohring, 1990)

Így például az ismert Boole-típusra:

````coq
Require Import Lia.

Fixpoint összeg (n:nat) :=
match n with 
  | 0 => 0
  | S n => (összeg n) + S n
end.

Theorem első_n_szám_összege : forall n, 2*(összeg n) = n*(n+1).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
simpl in IHn.
lia.
Show Proof.
Qed.
````

