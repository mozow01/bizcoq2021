
## Összefoglaló
A "típus" a "halmaz" nagytestvére, csak típusból végtelen sok fajta van, típusok végtelen hierachiája. 

Induktív típusok kezdőelemek felhasználásával építkezős módon keletkeznek, az építőelemeik a **konstruktorok.** Például a HF-beli szavak típusnak két konstruktora van:

````coq
Inductive szavak : Set :=
   | Hello : szavak -> szavak
   | world : szavak.
````

Proof Mode-ban, ha adott típus elemét kell megadni, akkor (természetesen) a típus konstruktorjaival legyártható elemeket kínálunk fel a cél számára, az ````apply "konstruktorneve".```` vagy ````constructor n.```` taktikával (n kisebb vagy egyenlő a konstruktorok számánál). Ha pl. eléggé el nem ítélhető módon egy mondatot akarunk definiálni, aminek a szavai "Hello world", akkor ezt megtehetjük így is:

````coq
Definition mondat_1 : szavak.
  constructor 1.
  constructor 2.
  Show Proof.
Defined.

Definition mondat_2 : szavak.
  apply Hello.
  apply world.
Defined.
````
Ha indukciós szabályra akarunk hivatkozni, akkor megtehetjük az ````apply Type_ind.```` mellett az ````induction x```` szabállyal is, ahol Type a szóban forgó típus, x a változó, amire indukálni akarunk. (Erre láttunk már példát, de azokat lehet egymás után kiadott indukciós szabályokkal is. Az alábbiakban az ````auto```` taktika egy Coq-ba beépített automatikus bizonyításkeresési eljárás.)

````coq
Theorem DM_2 : (forall x y : Boole, (nem x) es (nem y) = nem (x vagy y) ).
Proof. 
  induction x, y.
  auto.
  auto.
  auto.
  auto.
Qed.
````

## Véges típusok



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



