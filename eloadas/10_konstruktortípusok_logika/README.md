# Konstruktorok típusai, logika

## Az induktív konstruktciók kalkulusa és a finitizmus

### Mi az hilberti finitizmus?

Alapvetően a primitív rekurzív aritmetika (PRA), azaz 

1. _Alapfüggvények:_ 0 : N, S _ : N -> N
2. _Primitív rekurzió:_ F : N -> N értelmezett, ha 
  * 1. F(0) primitív rekurzívan értelmezett, és 
  * 2. van primitív rekurzívan értelmezett g : N -> N -> N, hogy F(S n) = g(n, F(n)).
3. _Helyettesítés:_ Ha h : N -> N -> N p.r. és f(), g(): N -> N, akkor g(f(),h()) is pr. 
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

**Fő példa finit érvelésre:**

> Minden p prímre létezik prím a (p, p! + 1] intervallumban. 

(Ha ugyanis nem lenne ilyen prím, akkor p! + 1 -et egy szám sem osztaná az (1, p!] intervallumból, mert az (1, p]-beli összes számmal osztva 1-ek kapunk maradékul, (p, p! + 1)-ben meg az indirekt feltevés miatt nincs prím, így ezek sem osztják, így p! + 1 prím, ami ellentmond az indirekt feltevésnek. Megjegyzés: a SZAT egy PRA-beli tétel.)

Megjegyzés: P(x) = "x prím és létezik y prím, hogy x < y ≤ x! + 1" eldönthető predikátum, persze naiv módon, legfeljebb x! esetben kell ellenőrizni, hogy valami prím-e, ami a futási időre nézve extrém magas felső korlát. De legalább van neki korlátja! :)

Ezzel szemben _alapból,_ nem eldönthető (csak a fortiori az előző miatt), hogy ,,létezik x-nél nagyobb prím''. 

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

## A kiszámíthatóságot garantáló feltételek
<!--- 
### Jólfundáltsági feltétel

Kíséreljünk meg rekurzióval _definiálni_ egy f ( _ _ _ ) függvényt, ami T típusú. Ezt valami egyenlettel gondoljuk megtenni:

> f (a, b, c) := g ( f (d, e, h) )

ahol **1.** f nem szerepel g-ben és **2.** amikor g-t f (d, e, h) -re alkalmazzuk, akkor de d, e, h alacsonyabb _konstrukciós_ bonyolultságú, mint a, b, c, azaz d, e, h -re már rekurzívan definiált (megkonstruált) f. 

Ezek az induktívan definiált típusokra is igazak, vagyis azokra a típusokra, amelyekben az a, b, c, d, e, h konstrukciók laknak. Legyen T ( _ _ _ ) egy paraméteres típus, amit rekurzióval definiálunk, azaz megadunk cons konstruktorokat, amik T ( _ _ _ ) -beli lakókat gyártanak le, pl. Backus--Naur-jelléssel (itt a konstruktor nincs feltüntetve):

> T (A, B, C) ::= ... | cons ( T (A, B, C) ) | ...

illetve a lakókat általános t (A, B, C) : T (A, B, C) jelöléssel feltüntetve:

> t(A, B, C) ::= ... | const ( t (A, B, C), ... ) | ...

Pl. Coq jelöléssel, mondjuk a vagy (ebben nincs rekurzió)

````coq
Inductive or (A B : Prop) : Prop :=
    | or_introl : A -> A \/ B 
    | or_intror : B -> A \/ B.
````

BNF-ben:

> t (A, B) ::= or_intro (A) | or_intror (B) 

illetve a nat lista:

````coq
Inductive list (A : Type) : Type :=
    | nil : list A 
    | cons : A -> list A -> list A
````

BNF-ben:

> t (A) ::= nil | cons (A) ( t (A) )


-->

### Végtelen ciklus rekonstrukció nem szigorúan pozitív előfordulás miatt

Legyen 

````coq 
*Inductive T : Type :=
| App : T -> T -> T
| Lam : (T -> T) -> T.
````
itt T neve termek típusa, Lam egy olyan konstrukció, ami egy függvényből termet csinál (Lam f : T, ha f : T -> T)

````coq 
*Definition ω : T -> T := fun x =>
  match x with
    | Lam f => f x
    | _ => x
  end.
````

Ekkor 

````coq 
*ω (Lam ω) =ζcbn (fun x => match x with | Lam f => f x | _ => x end) Lam ω  
           =β Lam ω with | Lam f => f Lam ω | _ => Lam ω end 
           =ι ω (Lam ω)
````

### Pozitivitási feltétel

Egy induktív T típus konstruktorai ilyen típusúak tudnak lenni:

> A_1 -> A_2 -> --- -> A_n -> T

ahol -- függő típusokat elfelejtve -- ahol T (ami azért paraméterektől függhet) pozitívan szerepel A_1 -> A_2 -> ... -> A_n -> T -ben.

T _pozitívan szerepel_ A-ban, ha

1. A = T = atomi,
2. A = U -> V, és U-ban T szigorúan pozitívan szerepel és V-ben pozitívan szerepel.

T _szigorúan pozitívan szerepel_ A-ban:

1. ha nem szerepel benne :) 
2. A = T = atomi
3. A = U -> V, és T az U-ban nem szerepel, V-ben pedig szigorúan pozitívan szerepel.

**Példa:**

````coq 
Inductive T : Type 
  | furi : nat -> (T -> nat) -> T.
````

olyan, hogy T nem pozitívan szerepel T -> nat-ban (T szerepel T-ben, azaz nem szigorúan pozitívan szerepel).

````coq 
Inductive T : Type 
  | nemfuri : nat -> (nat -> T) -> T.
````

nat -> (nat -> T) -> T -ban T pozitívan szerepel.

## Reflection

Reflectionnek nevezzük, amikor az elég gazdag nyelv, jelen esetben a Coq egy töredékét a szemantikai rendszerével együtt modellezzük a nyelven belül. 


