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

A nat típusnál maradva, létezik a nat_ind szabály, amelyet a

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

Hát, nem a "Hello, world!", de épp az, amire számítani lehetett :sweat_smile:

Megjegyzés: később meg fogjuk beszélni, hogy A->B->C pont azt jelenti, amit (A/\B)->C. Amikor (A/\B)->C -ból A->B->C -t csinálunk, azt *curryingnek* nevezik és ez egy jól ismert technika az abszrakt algebrában. Ugyanez A->B->C -ból (A/\B)->C irányba az *uncurrying*. Amúgy az A->B->C kifejezés az A->(B->C) zárójelezést rövidíti, azaz -> jobbra asszociált. 

## Beetetés: Boole-típus

Ismerős a kétértékű logika. De mi nem ezt fogjuk játszani. Ennek ellenére érdemes megnézni, mert az egyik legegyszerűbb induktví típus.

```coq
Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.
```
