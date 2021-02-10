# Bevezetés

## Induktív konstrukciók?

Amit most tanulni fogunk, azt az induktív konstrukciók kalkulusa egy szoftveres implementációjának is nevezik. 

Ha arra vagyunk kíváncsiak, hogy mi a fő gondolat az induktív konstrukciók mögött, akkor a legalkalmasabb példa erre a teljes indukció sémája:

> <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP(0)%5Cqquad%20(%5Cforall%20n%3A%5Cmathrm%7Bnat%7D)(P(n)%5Cto%20P(n%2B1))%7D%7B(%5Cforall%20n%3A%5Cmathrm%7Bnat%7D)P(n)%7D">

Értjük! De milyen dolgokról beszél ez a szabály? Ezt rögzíti a ritkán kiírt két másik posztulátum:

> <img src="https://render.githubusercontent.com/render/math?math=%5Cbegin%7Balign*%7D%0A%26%200%20%20%26%20%26%3A%5Cmathrm%7Bnat%7D%5C%5C%0A%26%20%5C_%2B1%20%20%26%20%26%3A%5Cmathrm%7Bnat%7D%5Cto%20%5Cmathrm%7Bnat%7D%0A%5Cend%7Balign*%7D">

És miféle dolog <img src="https://render.githubusercontent.com/render/math?math=P">?

> <img src="https://render.githubusercontent.com/render/math?math=P%3A%20%5Cmathrm%7Bnat%7D%5Cto%20%5Cmathrm%7BProp%7D">

És <img src="https://render.githubusercontent.com/render/math?math=%5Cmathrm%7Bnat%7D"> és <img src="https://render.githubusercontent.com/render/math?math=%5Cmathrm%7BProp%7D">?

> <img src="https://render.githubusercontent.com/render/math?math=%5Cbegin%7Balign*%7D%0A%26%5Cmathrm%7Bnat%7D%20%26%20%26%3A%20%5Cmathrm%7BType%7D%5C%5C%0A%26%5Cmathrm%7BProp%7D%20%26%20%26%3A%20%5Cmathrm%7BType%7D%0A%5Cend%7Balign*%7D">

Ezzel meg is érkezünk a típuselmélet világába.

>> Az induktív *T* típus és ennek *t* lakói (jelben: *t : T*) olyan kifejezések, amelyek teljesítik, hogy   
>>
>> 1. *T* összes lakója egységes, véges sok konstrukciós szabály segítségével gyártódik le,
>> 2. *T* összes lakójára vonatkozóan egységes tulajdonságokat fogalmazhatunk meg vagy ezek felett függvényeket definiálhatunk *T* indukciós ill. rekurziós szabályának segítségével ([olvasmány](https://www.cs.cmu.edu/~fp/papers/mfps89.pdf) p. 4.).

A nat típusnál maradva, létezik ennek is az indukciós szabálya, amelyet a

```coq
Print nat_ind.
```

paranccsal írathatunk ki és kapjuk (lényegében) a következő szabályt:

```coq
(*Message:
fun P : nat -> Prop => nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n  *)
```

Hát, nem a "Hello, world!", de épp az, amire számítani lehetett :sweat_smile: Ez a teljes indukció sémája.

Megjegyzés: később meg fogjuk beszélni, hogy A->B->C pont azt jelenti, amit (A/\B)->C. Amikor (A/\B)->C -ból A->B->C -t csinálunk, azt *curryingnek* nevezik és ez egy jól ismert technika az abszrakt algebrában. Ugyanez A->B->C -ból (A/\B)->C irányba az *uncurrying*. Amúgy az A->B->C kifejezés az A->(B->C) zárójelezést rövidíti, azaz -> jobbra asszociált. 

A nat, a természetes számok halmaza, egy induktív adattípus, és a konstrukciós szabályai, voltaképpen az (induktív) definíciója:

```coq
Print nat.
```

```
(*Message:
Inductive nat : Set :=  
     | O : nat 
     | S : nat -> nat. *)
```

## Figyelemelterelés: Boole-típus

Ismerős a kétértékű logika. De mi nem ezt fogjuk játszani. Ennek ellenére érdemes megnézni, mert az egyik legegyszerűbb induktví típus.

```coq
Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.
```

A Coq automatikusan generálja az indukciós szabályát (de majd megpróbáljuk később mi is legyártani):

```coq
Print Boole_ind.
```

```coq
(*Message:
fun P : Boole -> Prop => Boole_rect P
     : forall P : Boole -> Prop, P igaz -> P hamis -> forall b : Boole, P b *)
```

Gondoljuk végig, hogy ez mit jelent! Most definiáljuk a Boole műveleteket és tételeket igazolunk rájuk vonatkozóan:

```coq
Definition Boole_Or (b1: Boole) (b2: Boole) : Boole := 
  match b1 with 
    | igaz => match b2 with 
                | igaz => igaz 
                | hamis => igaz 
              end
    | hamis => match b2 with 
                | igaz => igaz 
                | hamis => hamis
               end
  end.
  
Notation "x 'vagy' y" := (Boole_Or x y) (at level 20) : type_scope.  
```

Vegyük észre, hogy a Boole_Or nevű függvényt (ami Boole -> Boole -> Boole típusú konkstrukció) a Boole típus szerkezetére vonatkozó módon definiáltuk. (b1, b2 úgy nevezett *paraméterek*, de most ez mindegy.)

```coq
Definition Boole_And (b1 : Boole) (b2: Boole) : Boole := 
  match b1 with 
    | igaz => match b2 with | igaz => igaz | hamis => hamis end
    | hamis => match b2 with | igaz => hamis | hamis => hamis end 
    end.

Notation "x 'es' y" := (Boole_And x y) (at level 20) : type_scope.

Definition Boole_Not (b : Boole) : Boole := 
  match b with 
    | igaz => hamis 
    | hamis => igaz
  end.

Notation "'nem' x" := (Boole_Not x) (at level 20) : type_scope.
```
Igazoljuk a kizárt haramdik elvét és a de Morganból az egyiket!

```coq
Theorem LEM : (forall x : Boole, x vagy (nem x) = igaz). 
Proof.
  intros.
  Print Boole_ind.
  apply Boole_ind with (P:= fun x => x vagy (nem x) = igaz).
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  Show Proof.
Qed.
```

```coq
Theorem DM_1 : (forall x y : Boole, (nem x) vagy (nem y) = nem (x es y) ).
Proof. 
  intros.
  apply Boole_ind with (P:=fun x => (nem x) vagy (nem y) = nem (x es y)).
  apply Boole_ind with (P:=fun y => (nem igaz) vagy (nem y) = nem (igaz es y)).
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  apply Boole_ind with (P:=fun y => (nem hamis) vagy (nem y) = nem (hamis es y)).
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  Show Proof.
Qed. 
```


Persze van bool:
```coq
SearchAbout bool.
```

## Gyakorló házi feladatok

1. Definiáljuk a ```Boole_imp``` (ha..., akkor...) és ```Boole_csa``` (... akkor és csak akkor, ha ...) függvényeket! Igazoljuk, hogy 

a) ```forall x y : Boole, (Boole_imp x y) = ((nem x) vagy y)```

b) ```forall x y : Boole, Boole_csa (Boole_imp x y) ((nem x) vagy y) = igaz```

2. Igazoljuk, hogy ```forall x y : Boole, ((nem x) es (nem y)) = nem (x vagy y)```.


## Izgibb házi feladatok

(Itt bool már a Coq beépített Boole-típusa, lásd: SearchAbout bool.)

3. Definiáljuk az ```f_1 : (bool -> bool) -> bool``` függvényt, amely egy ```g : bool -> bool``` esetén az

```f_1 g``` := ```andb (g(igaz)) (g(hamis))```
     
értéket adja vissza. Számítsuk ki ```f_1(fun x : bool => orb x (notb x))``` értékét!

4. Definiáljunk egy "```szavak```" induktív típust, ami alkalmas arra, hogy az ```Eval compute in (???)``` parancs esetén a "```Hello world```" kimenetet jeleníti meg. 

5. Definiáljuk az ```f_2 : (bool -> bool -> bool) -> bool``` függvényt, amely egy ```g : bool -> bool -> bool``` esetén az

```f_2 g``` := ```andb (f_1(g(igaz))) (f_1(g(hamis)))``` 

értéket adja vissza. Számítsuk ki ```f_2(fun x : bool => orb x y)``` és ```f_2(fun x : bool => impb (orb (notb x) (notb y)) (notb andb x y) )``` értékét!

