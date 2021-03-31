# Logikai típusok, indukciós elvek

A Coq a CIC-et (Calculus of Inductive Construction-t) implementálja. Magelméletének levezetési szabályai közül az leglényegesebbek:

|Pi formációs szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%3AType%5Cquad%5Cquad%20%5CGamma%2Cx%3AA%5Cvdash%20B%3AType%7D%7B%5CGamma%5Cvdash%20%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%3AType%7D">
---------|-------

 Pi bevezetési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%3AType%5Cquad%5Cquad%20%5CGamma%2Cx%3AA%5Cvdash%20M%3AB%7D%7B%5CGamma%5Cvdash%20%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%7D"> 
 -------|------

Pi kiküszöbölési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20M%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%5Cquad%5Cquad%20%5CGamma%20%5Cvdash%20N%3AA%7D%7B%5CGamma%5Cvdash%20M%20N%20%3A%20B%5Bx%2FN%5D%20%7D">
----- | -----

Pi komputációs szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM%3A%5CPi%5C!%20x%5C!%3A%5C!%20A.%5C%3B%20B%20%5Cquad%5Cquad%20%5CGamma%20%5Cvdash%20N%3AA%7D%7B%5CGamma%5Cvdash%20(%5Clambda%20%5C!x%5C!%3A%5C!A.%5C%2CM)%20N%20%5C%3B%5Cto_%5Cbeta%20%5C%3BM%5Bx%2FN%5D%3AB%5Bx%2FN%5D%20%7D"> 
-------|--------

## Implikáció és konjunkció

Ha B nem függ x-től (B-ben nem szerepel vagy nem szerepel szabadon x, pl. a ````nat```` típus konstans, abban nincsenek változók) és B állítástípusú ````Prop```` (pl. ````A/\B : Prop```` és A, B csak _paraméter,_ ezért nem függő típus), akkor a fenti képletek átmennek a ,,ha..., akkor... '' szabályaiba:

-> bevezetési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Ccup%20%5C%7Bx%3AA%5C%7D%5Cvdash%20f(x)%3AB%20%7D%7B%5CGamma%5Cvdash%5Clambda%20x.f(x)%3AA%20%5Cto%20B%7D">
 -------|------

-> kiküszöbölési szabálya: | <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20f%3AA%5Cto%20B%5Cquad%20%5CGamma%5Cvdash%20a%3AA%20%7D%7B%5CGamma%5Cvdash%20fa%3AB%7D">
 -------|------
 
 -> komputációs szabálya: | <img src="https://render.githubusercontent.com/render/math?math=(%5Clambda%20x.f(x))%5C%2Ca%5C%3B%5Cto_%5Cbeta%5C%3B%20f(a)">
 -------|------
 
A további logikai konnektívumokat is fel tudjuk venni nyelvbe, az ````Inductive```` parancs segítségével, a bevezetési szabályuk alapján. Így például az "és" bevezetési szabálya:

````coq
Inductive and (A B : Prop) : Prop :=  
    | conj : A -> B -> A /\ B
where "A /\ B" = and A B.
````

Ha most a prooftermekről elfeledkezünk és csak az állításokat hagyjuk meg, akkor: 

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cquad%20%5CGamma%5Cvdash%20B%7D%7B%5CGamma%5Cvdash%20A%20%5Cwedge%20B%7D">

Hagyományosan, a kiküszöbölési szabály ez lenne: 

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%20%5Cwedge%20B%7D%7B%5CGamma%5Cvdash%20A%7D%5Cquad%20%5Cdfrac%7B%5CGamma%5Cvdash%20A%20%5Cwedge%20B%7D%7B%5CGamma%5Cvdash%20B%7D">

A Coq mégsem ezt választja, hanem indukciós szabályt generál(!) és ez lesz belőle (most csak az ````and_ind```` induktor típusát tekintve):

````coq
forall A B P : Prop, (A -> B -> P) -> A /\ B -> P
````
 
vagy ha visszafordítjuk bizonyításelméleti fává:
 
 <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%20%5Cwedge%20B%5Cquad%20%5CGamma%5Ccup%5C%7BA%2CB%5C%7D%5Cvdash%20P%20%7D%7B%5CGamma%5Cvdash%20P%7D">
 
 Mind a kettő jó, mert ekvivalensek.
 
 Figyeljünk fel arra, hogy a Coq nem elégszik meg a saját implikációjának induktorával. Ha megkérdezzük tőle, hogy az alábbi konnektívumnak mi a kiküszöbülési szabálya a következőket válaszolja:
 
 ````coq
Inductive Impl (A B:Prop) : Prop :=
  Lam : (A -> B) -> Impl A B.

Print Impl_ind.

(* : forall A B P : Prop, ((A -> B) -> P) -> Impl A B -> P*)
 ````

Ez nem is szokásos és nehezen ábrázolható szabály (még a bizonyításelmélet tárgyalások sem használják):

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%0A%26%20A%5C%5C%0A%26%20%5Cvdots%5C%5C%0A%26%20B%5C%5C%0AA%20%5Cto%20B%20%26%20%5Coverline%7BP%7D%0A%5Cend%7Bmatrix%7D%20%7D%7BP%7D">, ha valamit, akkor inkább ezt: <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5CGamma%5Cvdash%20A%5Cto%20B%20%5Cquad%20%5CGamma%5Cvdash%20%20A%5Cquad%20%5CGamma%5Ccup%5C%7BB%5C%7D%5Cvdash%20P%20%7D%7B%5CGamma%5Cvdash%20P%7D">

ennek ellenére szintén belátható, hogy ekvivalens a modus ponens-szel.

## Használatelmélet - egy pici filozófia

A bevezetési és kiküszöbölési szabályok rendszeréhez (ezt természetes levezetési rendszernek nevezzük), leginkább egy olyan jelentéselmélet tartozik, amit a nyelvfilozófiában _használatelméletnek_ neveznek. A használatelmélet szerint egy adott szó jelentése a használatában rejlik. Így van ez a logikai szavakkal is. Egy ilyen jelentés két részből áll.
- a verifikációs jelentésrész azt mondja meg, hogy ha egy mondatban szerepel, akkor mi mondat állításának feltétele
- a pragmatista jelentésrész azt mondja meg, hogy mire tudunk belőle következtetni.

Gerhard Gentzen sejtette meg először, hogy a bevezetési szabályok meghatározzák a kiküszöbölési szabályokat. A Coq ezt a paradigmát követi. A bevezetési szabályból algoritmikusan generálja a kiküszöbölési (indukciós) szabályt.

## Hogyan határozza meg a bevezetési szabály a kiküszöbölésit?


 
 ## Az axiómák hátrányairól
 
 Nem csak arról van szó, amiről Russell írt 1919-ben: 
 
 > Az általunk kívánt ,,posztulálás'' módszerének számos előnye van; nem mások, mint a tolvajlás előnyei a tisztességes munkával szemben. :joy:

Hanem arról, hogy az axiómáknál a komputáció elakad. Tekintsük ugyanis a következőket. 

````coq
Axiom NAT_dec : forall n m : nat, {n=m} + {n<>m}.

Definition char_2 (n : nat) : nat :=
if (NAT_dec n 2) then 1 else 0.

Eval compute in char_2 2.

(* = if NAT_dec 2 2 then 1 else 0
     : nat *)

Require Import Arith.

Definition char_2' (n : nat) : nat :=
if (Nat.eq_dec n 2) then 1 else 0.

Eval compute in char_2' 2.
 
(* = 1
     : nat*)
````

Míg ````NAT_dec```` csak deklarálva van (axiómaként), addig ````Nat.eq_dec```` rekurzív/konstruktív módon van definiálva (lásd ````Print Nat.eq_dec````).

Világos, hogy a probléma elméleti. Ha ````t : nat -> nat````-t csak deklaráljuk, akkor a ````t 2```` term nem redukálható tovább, azaz elakad a komputációs út. Ha azonban megvan az a mondjuk ````fun x => S x```` függvény, amit ````t```` jelöl, akkor 

> ````t 2    =    (fun x => S x) 2  ------>  S 2```` 

````S 2```` már egy olyan, amit egy számítás eredményeként várunk, azaz a 3 term.   

Ezért van az, hogy az induktív konstrukciók kalkulusában **nincsenek axiómák, csak levezetési szabályok.**

Egyben azt is láttuk, hogy a beta-redukciónak nem csak elméleti jelentőssége van, hanem gyakorlati. Az ````fun x => f x```` alakú termek a programoknak felelnek meg, a program futtatásának egy ````a```` inputon pedig a beta-redukció:

````coq
((fun x => f x) a) = f a
````
