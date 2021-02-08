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

Gondoljuk végig, hogy ezt mit jelent! Most definiáljuk a Boole műveleteket és tételeket igazolunk rájuk vonatkozóan:

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

Persze van bool:
```coq
SearchAbout bool.
```

## Természetes számok

Ez egy elég kemény dió. Sok csomag és taktika van, ami ezzel küzd: omega, crush, Mathematical Components.

```coq
SearchAbout plus.

Theorem n_plus_O : forall n : nat, n + O = n.
Proof. 
  intros.
  induction n.
  unfold plus.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Show Proof.
Qed.
```

## Fák, bokrok, ligetek

```coq
Inductive tree : Set :=
  | l : tree
  | n : tree -> tree -> tree.

Fixpoint length (t:tree) : nat :=
  match t with
    | l => 1
    | n t1 t2 => (length t1) + (length t2) end. 

Theorem levelhossz : length(l)=1.
Proof. 
  unfold length.
  reflexivity.
Qed.

Fixpoint right (t s : tree) : tree :=
  match t with
    | l => n l s
    | n t0 t1 => n t0 (right t1 s) end. 

Eval compute in right (n l l) (n l (n l l)).

Theorem ossz_tree : forall t s : tree, length (right t s) = length t + length s.
Proof.
  intros.
  induction t.
  simpl.
  reflexivity.
  simpl.
  rewrite IHt2.
  Require Import Omega.
  omega.
Qed.

Theorem ossz_tree_ll : length (right l l) = length l + length l.
Proof.
  apply ossz_tree with (t:=l) (s:=l).
Qed.
```


