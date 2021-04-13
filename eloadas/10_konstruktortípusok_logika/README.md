# Kostruktorok típusai, logika

## Az induktív konstruktciók kalkulusa és a finitizmus

### Mi az hilberti finitizmus?

Alapvetően a primitív rekurzív aritmetika, azaz 

1. _Alapfüggvények:_ 0 : N, S _ : N -> N
2. _Primitív rekurzió:_ F : N -> N értelmezett, ha 
  * 1. F(0) primitív rekurzívan értelmezett, és 
  * 2. van primitív rekurzívan értelmezett g : N -> N -> N, hogy F(S n) = g(n, F(n)).
3. _Helyettesítés:_ Ha h : N -> N -> N p.r. és f(), g(): N -> N, akkor g(f(),g()) is pr. 
4. _Projekció:_ N -> N -> ... -> N : (a, b, c, ...) |---> b pr.

(Ez Tait-tézise. Ami ugyan történetileg cáfolható, mert Hilbert nézete változott és a poszt-Gödel érában a transzfinit rekurziót is finitként értette, de filozófiailag alátámasztható (megérvelhető) az állítása.)

És valóban. Nézzük, mikor van egy P : nat -> **Type** függvény értelmezve: 

````coq
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
````
És minden induktív típus feletti függvény ilyen szellemben van értelmezve, azaz rekurzorral.

### Az axiómák hátrányairól -- miért természetes levezetés és nem Hilbert-féle felépítés
 
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
