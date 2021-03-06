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

## Használatelmélet -- egy pici filozófia

A bevezetési és kiküszöbölési szabályok rendszeréhez (ezt természetes levezetési rendszernek nevezzük), leginkább egy olyan jelentéselmélet tartozik, amit a nyelvfilozófiában _használatelméletnek_ neveznek. A használatelmélet szerint egy adott szó jelentése a használatában rejlik. Így van ez a logikai szavakkal is. Egy ilyen jelentés két részből áll.
- a verifikációs jelentésrész azt mondja meg, hogy ha egy mondatban szerepel, akkor mi mondat állításának feltétele
- a pragmatista jelentésrész azt mondja meg, hogy mire tudunk belőle következtetni.

Gerhard Gentzen sejtette meg először, hogy a bevezetési szabályok meghatározzák a kiküszöbölési szabályokat. A Coq ezt a paradigmát követi. A bevezetési szabályból algoritmikusan generálja a kiküszöbölési (indukciós) szabályt.

## Hogyan határozza meg a bevezetési szabály a kiküszöbölésit?

A kiküszöbölési szabályok közül induktívnak, vagy általános kiküszöbölési szabálynak nevezzük azt, ami arról beszél, hogy a definiált típus esetén minek kell teljesülnie, hogy egy tulajdonság a típus összes lakójára igaz legyen. Az elv az, hogy 

> ha a típus összes konstruált lakója teljesíti P-t, akkor minden lakója teljesíti P-t.

Az indukciós elvek alapvető szerkezete a következő:

<img src="https://render.githubusercontent.com/render/math?math=%5Cunderset%7B%5Cmathrm%7Bhead%7D%7D%7B%5Cforall%20A_1%5Cdots%20%5Cforall%20A_k%5Cforall%20P%3A%5Cforall%20x_1%5Cdots%20%5Cforall%20x_l%2CT(A_1%2C%5Cdots%2C%20A_k%2Cx_1%2C%5Cdots%2C%20x_l)%5Cto%20Prop%7D%2C%5Cquad%0A%5Cunderset%7B%5Cmathrm%7Bprinciple_premiss%7D%7D%7B%5Cforall%20x_1%5Cdots%20%5Cforall%20x_l%20P(C_i(A_1%2C%5Cdots%2C%20A_k%2Cx_1%2C%5Cdots%2C%20x_l))%7D%5Cdots%2C%5Cquad%5Cto%20%5Cunderset%7B%5Cmathrm%7Bepilogue%7D%7D%7B%5Cforall%20y%3A%5Cforall%20x_1%5Cdots%20%5Cforall%20x_l%3AT(A_1%2C%5Cdots%2C%20A_k%2Cx_1%2C%5Cdots%2C%20x_l)%2C%20P%5C%2Cy%7D">

Nem függő (de paraméteres) típusok esetén:

<img src="https://render.githubusercontent.com/render/math?math=%5Cunderset%7B%5Cmathrm%7Bhead%7D%7D%7B%5Cforall%20A_1%5Cdots%20%5Cforall%20A_k%5Cforall%20P%3AT(A_1%2C%5Cdots%2C%20A_k)%5Cto%20Prop%7D%2C%5Cquad%0A%5Cunderset%7B%5Cmathrm%7Bprinciple_premiss%7D%7D%7BP(C_i(A_1%2C%5Cdots%2C%20A_k))%7D%5Cdots%2C%5Cquad%5Cto%20%5Cunderset%7B%5Cmathrm%7Bepilogue%7D%7D%7B%5Cforall%20y%3AT(A_1%2C%5Cdots%2C%20A_k)%2C%20P%5C%2Cy%7D">

ahol T a definiált típus, C_i pedig a T típus konstruktorai. 

**1. Példa** polimorf lista típus:

````coq
Inductive list (A : Type) : Type :=
    nil  : list A | 
    cons : A -> list A -> list A.
````

A _fej_ (prológus) ilyenkor az egyetlen paraméter és a predikátum felett kvantifikál:

````coq
forall (A : Type) (P : list A -> Prop),
````

A _főpremissza_ úgy keletkezik, hogy az először az összes egyik majd a másik konstruktorral keletkezett elemről teszi fel, hogy teljesül rá P

````coq
P nil -> (forall (a : A) (l : list A ) (p : P l ), P (cons a l)) -> 
````

Végül az _epilogus_ arról beszél, hogy list A minden eleme teljesíti P-t:

````coq
forall l : list A, P l
````

**2. Példa.** Szorzat típus:

````coq
Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B.
````

A _fej_ (prológus) ilyenkor a két paraméter és a predikátum felett kvantifikál:

````coq
forall (A B : Type) (P : A * B -> Prop),
````

A _főpremissza_ úgy keletkezik, hogy az összes konstruktorral keletkezett elemről teszi fel, hogy teljesül rá P

````coq
(forall (f : A) (g : B) P (pair f g)) -> 
````

Végül az _epilogus_ arról beszél, hogy list A minden eleme teljesíti P-t:

````coq
forall p : A * B , P p
````

**3. Példa.** Éredekes megjegyezni, hogy a konjunkciónak pontosan ugyanaz a definiíciója, csak nem Type-ba, hanem Prop-ba képez. Ekkor a Coq a Simplyfied Induction Principle-t adja ki alapból, azaz azt az esetet, amikor csak **konstans** P-re van kimondva az indukciós szabály. Propozíciók esetén ugyanis a konklúzió általában -- de nem mindig -- propzíció és nem valamely állítások bizonyításairól szóló predikátum.

````coq
forall A B P : Prop, (A -> B -> P) -> A /\ B -> P
```` 

Ez tehát nemkonstans P esetén ez lenne: 

````coq
forall (A B : Prop) (P : A /\ B  -> Prop), (forall (a : A) (b : B) P (conj a b)) -> (forall p: A /\ B) P p.
```` 
Világos, hogy ha P konstans, azaz P nem függ p-től, hanem mondjuk Q, akkor a kvantifikációból implikáció lesz, azaz ````(forall p: A /\ B) P p```` -ből ````A /\ B -> Q````.


## Házi feladatok

1. Definiáljuk a következő logikai típust: 

````coq
Reserved Notation "A 'wimp' B" (at level 99).

Inductive WImp (A B : Prop) : Prop :=
  | wl : ~A -> A wimp B
  | wr : ~~B -> A wimp B
where "A 'wimp' B" := (WImp A B) : type_scope.

Print WImp_ind.
````
(itt ~ a negáció jele ( ````Print not.```` )).

a) Igazoljuk, hogy 

````coq 
Theorem problem_1 : forall A B : Prop, A wimp B -> A -> ~~B.
````
(használjuk a ````contradiction.```` taktikát, ami formális ellentmondást keres a feltételek között).

b) Igazoljuk, hogy 

````coq
Theorem problem_2 : forall A B C: Prop, 
A -> A wimp (B wimp C) -> (~~(B wimp C)) wimp C -> ~~C.
````
(használjuk fel a ````problem_1```` -et.)

c) Vegyük fel axiómaként, hogy ````Axiom wmp : forall A B : Prop, A wimp B -> A -> ~~B.```` Igazoljuk, hogy ekkor (a WImp_ind szabály nélkül levezethető)

````coq
Theorem wimp_ind : forall A B P : Prop, (A \/ ~A) -> (~ A -> P) -> (~ ~ B -> P) -> (A wimp B) -> P
````

2. Adjunk meg olyan induktívan definiált "A simp B : Prop" típust (A B : Prop), amelynek kiküszöbölési szabálya:

````coq
forall A B P : Prop, ((A -> False) -> P) -> (B -> P) -> (A simp B) -> P
````

típusú!

3. Tanuljunk egy kis levezetésfákat!

[bizcoq_8.pdf](https://github.com/mozow01/bizcoq2021/blob/main/forrasok/bizcoq_8.pdf)  [bizcoq_8.tex](https://github.com/mozow01/bizcoq2021/blob/main/forrasok/bizcoq_8.tex) 

itt a tex file is, amiből el lehet sajátítani a levezetésfa LaTeX kódolást (NEM RÖHÖGNI, HOGY MILYEN BÉNA A LATEX-EM! :D )

leírtam annak a logikának a szabályait, amelyben a wimp kiküszöbölési szabály a wmp. 

a) Bizonyítsuk be csak wmp felhasználásával problem_2-t!

b) Értsük problem_2-t így: 

````
A, A wimp (B wimp C), (~~(B wimp C)) wimp C ⊦ ~~C
````

Rajzoljuk le akár kézzel, akár LaTeX-ben problem_2 levezetésfáját!
