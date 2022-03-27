#  A filozófia csodálatos hatékonysága az automatikus tételbizonyításban
Molnár Zoltán Gábor, Algebra Tsz.

## Coq automatikus bizonyító és bizonyításmenedzselő program

Thierry Coquand, Christine Paulin-Mohring implementálták számítógépesen az _Induktív Konstrukciók Kalkulusát_ (CIC, CoC, Coq), ami Peer Martin-Löf típuselméletének átdolgozása. 

## Mi az az induktív adattípus?

Alappélda: a **természetes számok** halmaza, mint rekurzívan definiált sorozat (nat).

_Konstruktorok:_

<img src="https://render.githubusercontent.com/render/math?math=0%3A%5Ctext%7Bnat%7D">

<img src="https://render.githubusercontent.com/render/math?math=S%3A%5Ctext%7Bnat%7D%5Cto%20%5Ctext%7Bnat%7D">

_Indukciós szabály:_

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP(0)%2C%5Cquad%20%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(n)%5Cto%20P(Sn)%7D%7B%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(n)%7D">

"Szemléletesen, egy induktívan definiált típus konstruktorok egy teljes listája által adott. A nekik megfelelő indukciós elvvel érvelünk a típus elemeivel kapcsolatban és a konstruktorokon függvényeket adunk meg, amik alkamasak az egész típus felett értelmezett primitív rekurzív függvények definiálására." (Christine Paulin-Mohring, 1990)

Így például az ismert Boole-típusra:

_Konstruktorok:_

<img src="https://render.githubusercontent.com/render/math?math=%5Cbegin%7Bmatrix%7D%5Ctext%7Btrue%7D%5C%3B%3A%5Ctext%7Bbool%7D%5C%5C%0A%5Ctext%7Bfalse%7D%3A%5Ctext%7Bbool%7D%0A%5Cend%7Bmatrix%7D">

_Indukciós szabály:_

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP(%5Ctext%7Btrue%7D)%5Cquad%20P(%5Ctext%7Bfalse%7D)%7D%7B%5Cforall%20b%3A%5Ctext%7Bbool%7D%2C%20P(b)%7D%0A">

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

