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
 
z:A ⊢ **K**zM

**Megjegyzés:** **K** és **S** a modus ponenszel együtt generálja az intuicionista implikációs logika hilberti felépítését: axiómák kódja **K**, **S** és egyetlen levezetési rendszer MP.

**Megjegyzés:** Az Y fixpont kombinátorról ne essék szó, mert a típusos lambda kalkulusban alapból ilyen nincs. De erről beszéltünk az induktív típusok definíciójánál. 

<!--
**Tételke.** Ha M kifejezés, melyben minden változó különböző, akkor minden összetett típusra létezik Γ, hogy Γ ⊢ M : A.

_Bizonyítás._ Strukturális indukcióval. 

_1._ Ha M = x, akkor M minden A típussal típusolható: x : A ⊢ x : A.

_2._ Ha M = PQ, (és minden változó különböző,) akkor tetszőleges B összetettre-re van Γ és Γ', hogy nincs bennük közös változó, és Γ ⊢ P : B → A és Γ' ⊢ Q : B. Így Γ, Γ' ⊢ PQ : A.

_3._ Ha M = λx.P, akkor legyen A = B->C összetett minden összetett C-re létezik Γ, hogy Γ ⊢ P : C. Ekkor vagy van Γ-ban x:A

-->
