# Véges típusok

## Ismétlés, összefoglalás
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
  induction x, y; auto.
Qed.
````

> A ````simpl. intuition. auto. tauto. trivial.```` parancsokkal automatizálni, gyorsítani tudjátok a bizonyításaitokat, definícióitokat. 

> A ````reflexivity```` parancs a **szó szerinti** azonosságokat, a ````discriminate```` parancs a **szó szerinti** különbözőségeket alakítja  belső egyenlőséggé (=) illetve belső különbözőséggé (<>). 

("Szó szerinti azonosság" itt azt jelenti, hogy külső, azaz nyelvi és nem tartalmi egyenlőség. Pl. 1+(1+1) szó szerint egyenlő saját magával, de (1+1)+1-gyel csak tartalmilag. Az más kérdés, hogy a típuselméletben egy külső azonosságra vezethető vissza a kettő.)

Példa program bizonyos szintű helyességbizonyítására (a korábban definiált Boole típus és Boole_And felhasználódik és a Szigma típus is.)

````coq 
Theorem And_thm : (forall (x y : Boole), { z: Boole | (x es y) = z /\ forall (w: Boole), ( (x es y) = w -> z=w)}).
(...) 

Definition sig_proj1 (A:Set) (P:A -> Prop) (x : sig P) : A :=
    match x with exist _ a _ => a end.

Definition sig_proj2 (A:Set) (P:A -> Prop) (x : sig P) : P(sig_proj1 A P x) :=
    match x with exist _ _ p => p end. 

Definition And_output (x y : Boole) := sig_proj1 Boole (fun z : Boole => ((x es y) = z /\ 
forall (w: Boole), ( (x es y) = w -> z=w))) (And_thm x y).

Definition And_proof (x y : Boole) := sig_proj2 Boole (fun z : Boole => ((x es y) = z /\ 
forall (w: Boole), ( (x es y) = w -> z=w))) (And_thm x y).
````

## Konkrét véges típusok

bool a kételemű típus volt. Példaként nézzünk egy háromelemű típust!

<img src="https://render.githubusercontent.com/render/math?math=%5Cmathbf%7BZ%7D_3%5E%2B%20%5Cequiv%20%5Cmathbf%7BZ%7D%2F3%5Cmathbf%7BZ%7D%2C%5C%3B%5C%3B%5C%3BZ_3%3D%5C%7B0%3B1%3B2%5C%7D">

Ez a hárommal való osztás maredékainak halmaza, illetve most tekintsünk erre úgy, hogy ő egy additív jelölésű csoport. Be fogjuk látni, hogy ez a maradékok összeadásával, a megfelelő inverz elemekkel és a 0-van, mint neutrális elemmel valóban csoportot alkot. Ezt a matematikusok kedvéért. A mérnökökkel azt nézzük meg, hogy ebben is (mind minden konstruktív megadású véges típusban) igaz, hogy az egyenlőség algoritmikusan eldönthető.

A Z_3 induktív típus:

````coq
Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.
````

Efelett a műveletek:

````coq
Definition ope x y :=
  match x , y with
  | n , y => y
  | x , n => x
  | a , b => n
  | b , a => n 
  | a , a => b
  | b , b => a
  end.

Definition inve x :=
  match x with
  | n => n
  | a => b
  | b => a
  end.
  ````
  
  Most belecsapunk a lecsóba és egy vegyes típust definiálunk egy Record-dal vagy Structure-rel:
  
  ````coq
  Structure Group : Type := const_kozos
{
  A : Set;

  op : A -> A -> A ;
  inv : A -> A ;
  z : A ;

  op_assoc : forall a b c, op a (op b c) = op (op a b) c;
  op_z : forall a, op a z = a /\ op z a = a ;
  op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
}.
  ````

**1.** Z_3 a megfelelő műveletekkel valóban a Group típus lakója.

````coq
Theorem Z_3_group : Group.
Proof.
  apply (const_kozos Z_3 ope inve n).
  induction a0, b0, c; compute; auto.
  induction a0; auto. 
  induction a0; auto.
Defined.
````

**2.** Az egyenlőség Z_3-ban (is) eldönthető.

````coq
Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
Defined.
````

Esetleg érdemes egy pillantást vetni arra, hogy melyik konstrukció igazolja az induktív konstrukciók kalkulusában Z_3 egyenlősége eldönthető:

````coq
Eval compute in Z_3_eq_dec a b.
````
````coq
or_intror
         (fun H : a = b =>
          match
            match
              H in (_ = y)
              return match y with
                     | n => False
                     | a => True
                     | b => False
                     end
            with
            | eq_refl => I
            end return False
          with
          end)
     : a = b \/ a <> b
````
HF: Megérteni ezt a programot!

Definiáltuk órán a **csoportmorfizmus** tulajdonságot is, amelyről [itt](bizcoq_2.v) a file. 
