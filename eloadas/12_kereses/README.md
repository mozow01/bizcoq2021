# Inhabitációs algoritmus folytatás

## Fő problémák

**Nyelv**

Típusok: A | A → B

Termek:  x | MN | λx.M

Kontextusok: . | Γ,x:A

A kontextus jól formált, ha minden változó típusa egyértelmű, azaz ha x:A, x:B &isin; Γ, akkor A = B.

**.. ⊢ .. : .. reláció:**

**Típusolás: **

|Var | App  | Lam |
|---|---|---|
| x:A &isin; Γ | Γ ⊢ M : A → B,   Γ ⊢ N:A | Γ,x:A ⊢ M : B |
 Γ ⊢ x:A| Γ ⊢ MN:B |  Γ ⊢ λx.M : A → B|
 
 Fő problémák:
 
 | Inhabitation | Type Check  | Typeability |
|---|---|---|
| Γ ⊢ ? : A  | Γ ⊢<sub>?</sub> M : A | Γ ⊢ M : ? |
 APTIME (=PSPACE) | PTIME | PTIME |
 
 **1.**  ⊢ λx.x : ? , ⊢ λx.λy.x : ? , ⊢ λx.λy.λz.xz(yz) : ?
 
 (**I** := λx.x, **K** := λx.λy.x , **S** := λx.λy.λz.xz(yz) kombinátorok)
 
**Megjegyzés:** Meglepő módon a típusolhatóság nem nehezebb probléma a típusellenőrzésnél. Az M zárt kifejezés pontosan akkor típusolható, ha tetszőleges A-ra:
 
z:A ⊢ **K**zM : A

**Megjegyzés:** **K** és **S** a modus ponenszel együtt generálja az intuicionista implikációs logika hilberti felépítését: axiómák kódja **K**, **S** és egyetlen levezetési szabály MP.

**Megjegyzés:** Az Y fixpont kombinátorról ne essék szó, mert a típusos lambda kalkulusban alapból ilyen nincs. De erről beszéltünk az induktív típusok definíciójánál. 

## Példák normalizációra, type check-ra és az inhabitációs algoritmus alkalmazására.

````coq
Parameter E F : Prop.

Parameter w : E.

Parameter y : E -> F.  

Eval cbv in ((fun z => ((fun x => (x z))y) ) w ).

Check (fun x y => x).

Check (fun (x : E) (y : F)  => x).

Theorem problem_1 : forall A B : Prop, (A -> B) -> ~ ( A /\ (~ B)).
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  apply H.
  apply H0.
Show Proof.
Qed.

Theorem problem_2 : forall A B C D : Prop, (A -> B) -> ( A /\ (B -> C) -> C).
Proof.
  tauto.
Qed.

Theorem problem_3 : forall A : nat -> Prop, (forall x, A x) -> ({ x | ~ A x } -> False).
Proof.
  intros.
  assert (K : ~ A (proj1_sig H0)). { exact (proj2_sig H0). }
  assert (L : A (proj1_sig H0)). { apply H. }
  contradiction.
Qed.
````

## Házi feladat

**1.** Igazoljuk, hogy 

````coq
Theorem problem_4 : forall A B : Prop, ((A -> B) -> A) -> (~ ~ A ).
````

és 

````coq
Theorem problem_5 : forall A B : Prop, ~ ~ (A \/ ~ A).
````

**2.** Igazoljuk, az inhabitációs algoritmus alkalmazásával, hogy az ````(A -> B) -> A -> (A -> C -> C)```` az egyszerű típusos lambda kalkulusban nem inhabitált!

**3.** Keressük meg (akár Coq-kal is) a λx.λy.λz.xz(yz) kifejezés típusát! Milyen logikai szabályt fejez ez ki?

 

<!--
**Tételke.** Ha M kifejezés, amelyben minden változószereplésben különböző változó áll, akkor van Γ és A, hogy Γ ⊢ M : A.

_Bizonyítás._ Strukturális indukcióval. 

_1._ Ha M = x, akkor minden A típussal x : A ⊢ x : A.
 -->




