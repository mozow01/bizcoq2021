# ZH feladatok

Az alábbiak közül **legalább 3 feladatban** kérek legalább **nemtriviális hozzájárulást** felmutatni. Ha a feladatokban a definíciók vagy tételek **nincsenek** szintaktikailag vagy szemantikailag **jól vagy rendesen kimondva,** akkor a feladathoz tartozik ennek helyes tisztázása. Ha bármelyik feladatnál célszerűbb más formális konstrukcióban tárgyalni a kérdést, akkor **válasszunk** egy **olyan** tálalást, **amiben kényelmesebb** dolgozni!

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
(A projektív síkon pontok, egyenesek és illeszkedés van. Bármely két különböző pontra egyetlen egyenes illeszkedik.  Emlékezzünk arra, hogy a pro

a) Igazoljuk, hogy 

````coq
forall p q : P, p <> q -> exists l : L, (I p l = true) /\ (I q l = true).
````
