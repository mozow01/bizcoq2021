# ZH feladatok

Az alábbiak közül **legalább 3 feladatban** kérek legalább **nemtriviális hozzájárulást** felmutatni. Ha a feladatokban részemről a definíciók vagy tételek **nincsenek** szintaktikailag vagy szemantikailag **jól vagy rendesen kimondva,** akkor a feladathoz tartozik ennek helyes tisztázása. Ha bármelyik feladatnál célszerűbb más formális konstrukcióban tárgyalni a kérdést, akkor **válasszunk** egy **olyan** tálalást, **amiben kényelmesebb** dolgozni!

**1. Irányítatlan hurokmentes gráf -- konstruktív felépítés**

Tekintsük az alábbi struktúrát, amelyben az élreláció Prop és nem bool kimenetű: 
````coq
Structure GraphConst : Type := make_GraphConst
{
  G :> Set;

  E : G -> G -> Prop ;

  undirected : forall a b, E a b -> E b a;
  noloop : forall a, ~ (E a a);
}.
````

a) Igazoljuk a 
````coq
Theorem triangle_free : exists G : UDLFGraph, (exists x y z : G, ((x<>y)/\ (y<>z) /\ (x<>z))
/\ (~(E G x y) \/ ~(E G y z) \/ ~(E G x z))).
````
tételt!

b) Igazoljuk a 
````coq 
Theorem triangle_has : exists G : UDLFGraph, (exists x y z w : G, ((x<>y)/\ (y<>z) /\ (x<>z))
/\ ((E G x y) /\ (E G y z) /\ (E G x z) /\ ~(E G x w))). 
````
c)
Definiáljunk egy legalább 10 csúcspontú véges **teljes**(!) gráfot a fenti értelemben. Igazoljuk, hogy ez valóban ````GraphConst````.

**2. Irányítatlan hurokmentes gráfok -- klasszikus eset** 

Tekintsük a következő struktúrát! (Itt az élreláció alapból eldöntehető, bool kimenetű.)

````coq
Structure GraphClassical : Type := make_GraphClassical
{
  G' :> Set;

  E' : G' -> G' -> bool ;

  undirected' : forall a b, implb (E' a b) (E' b a) = true;
  noloop' : forall a, negb (E' a a) = true;
}.
````
a) Definiáljuk egy gráf komplementerét! 

b) Definiáljuk azt a tulajdonságot, hogy valami komplementere valaminek. Igazoljuk, egy konkrét esetben, hogy két gráf komplemeter kapcsolatban van.

**3. Hat csúcspontú klasszikus egyszerű gráf**

Tekintsük a következő struktúrát!

````coq
Structure Hatcsucsu : Type := make_Hatcsucsu
{
  n :> nat;

  E'' :> nat -> nat -> bool ;

  hatcsucsu : n = 6;
  undirected'' : forall (a : nat) (b : nat), (a < 6 /\ b < 6) -> implb (E'' a b) (E'' b a) = true;
  noloop'' : forall (a : nat), (a < 6) -> negb (E'' a a) = true;
}.
````
a) Definiáljunk egy olyan függvényt, ami egy hat csúcspontú gráf egy csúcsának fokszámát határozza meg.

b) Definiáljuk a hatcsúcspontú gráf fokszámösszegét kiszámító függvényt!

c) (NEHÉZ) Igazoljuk, hogy a fokszámösszeg páros.

d) (NEHÉZ) Definiáljuk a hatcsucsu gráf komplementerét és igazoljuk, hogy vagy egy hatcsucsu gráfban van háromszög
 vagy a komplementerében. 

**4. Gyenge és gyengélkedésmentes projektív sík**

Tekintsük a következő struktúrát:

````coq
Structure WeakProjPlan : Type := make_WeakProjPlan
{
  P :> Set;

  L : Set;

  I : P -> L -> bool;

  points : forall p q : P, p <> q -> exists l : L, (I p l = true) /\ (I q l = true)
            /\ (forall k : L, ((I p k = true) /\ (I q k = true)) -> l=k);

  lines :  forall l k : L, l <> k -> exists p : P, (I p l = true) /\ (I p k = true);
  
  three_points : forall (l : L), exists (x y z : P), 
(I x l = true) /\ (I y l = true) /\ (I z l = true) /\ (x<>y)/\ (y<>z) /\ (x<>z) ;
}.
````
(A gyengus projektív síkon pontok, egyenesek és ezek között illeszkedés reláció van. Bármely két különböző pontra egyetlen egyenes illeszkedik. Bármely két különböző pontra egyetlen egyenes illeszkedik. Bármely két egyenesnek legalább egy közös pontja van. Minden egyenesen legalább három pontot tartamlaz. Emlékezzünk arra, hogy a projektív sík esetén létezik egy *dualitási* tulajdonság: ha az egyenes szót a pontra cseréljük, akkor a tételek érvényben maradnak.)

a) Adjunk meg ennek egy modelljét! Olyat is, amiben legalább két különböző egyenes van!

b) Igazoljuk, hogy 

````coq
forall p q : P, p <> q -> exists l : L, (I p l = true) /\ (I q l = true).
````
c)  Fogalmazzuk meg a four_points állítást: There exist at least four distinct points of which no three are collinear 
(collinear means they live in the same line). Igazoljuk, hogy 

d)  

````coq
forall l k : L, l <> k -> exists p : P, (I p l = true) /\ (I p k = true)
            /\ (forall q : P, ((I q l = true) /\ (I q k = true)) -> p=q)
````

e) (NEHÉZ) Four_point állítás felhasználásával igazoljuk, hogy 

````coq
forall (p : P), exists (l k m : L), (I p l = true) /\ (I p k = true) /\ (I p m = true) 
/\ (l<>k)/\ (k<>m) /\ (l<>m).
````

**5. Listák**

a) Definiáljuk egy nat értékeket felvevő lista összegét (használjuk az opcionális típust figyelve arra, hogy üres lista is lehet a bemenet).

b) ... minimumát. 

c) Definiáljuk az Argmin függvényt, mely (a:..., b:nat) párok listájához rendeli az opcionális olyan a értéket, amielyhez a legkisebb b érték tartozik.   

**6. Számok**

a) Definiáljunk egy nat -> bool függvényt, ami egy természetes számhoz pontosan akkor rendeli a true értéket, ha az a 3.

b) Definiáljunk egy nat -> bool függvényt, ami egy természetes számhoz pontosan akkor rendeli a true értéket, ha kisebb, mint 3.

c) Definiáljuk azt a nat -> nat -> bool függvényt, ami pontosan akkor rendeli egy (m:nat) (n:nat) bemenethez a true értéket, ha n>m.  
 
**7. Számok_2**

a) Definiáljuk azt a nat -> (nat -> nat) -> nat  függényt, ami egy n számhoz és f függvényhez hozzárendeli az f függvény leső n tagjának összegét.

b) Igazoljuk, hogy az első n természetes szám összegének kétszerese n*(n+1).

**8. Fák**

````Require Import ZArith.```` az egész számok elméletét hívja segítségül a Coq-ban.

a) Definiáljuk a bináris, ````Z```` (egész, de pozitív, negatív, nulla is) értékű számokat a címkéjükön hordozó Z_btree fákat.

b) Defniniáljuk azt a függvényt, ami egy Z_btree fához a true értéket rendeli, ha van a címkéi között 0 és a false-t, ha nincs benne 0. (Az összehasonlító függvény a ````Zeq_bool````).

c) Ugyanez nem nullával, hanem egy tetszőleges m számmal.
