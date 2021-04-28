# Inhabitációs algoritmus folytatás

## Fő problémák

**Nyelv**

Típusok: A | A → B

Termek:  x | MN | λx.M

Kontextusok: . | Γ,x:A

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

**Tételke.**  
