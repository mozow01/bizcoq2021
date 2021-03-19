# Absztrakt véges típus

Szükséges lehet alkalmazni, és Coq-ban implementálni is lehet, egy olyan függő típust, ami minden egyes *n* természetes számhoz hozzárendel egy ,,kanonikus'' *n* elemű véges típust. Például ez akkor jó, ha hivatkozni szereténk az összes véges típusra vagy szeretnénk korlátlan, de véges argumentumszámú függvényt vagy ennyi elágazásos fát. Ez a konstrukció a **Fin:**

````coq 
Inductive Fin : nat -> Set :=
  |fzero : forall {n:nat}, Fin (S n)
  |fsucc : forall {n:nat}, Fin n -> Fin (S n).
````

(A fentiekben a {...} zárójel azt jelzi, hogy az adott konstruktor azon bemenete rejtett paraméter és amennyiben lehetséges vagy nincs rá szükség, akkor a Coq kitalálja vagy ignorálja.)

## Fin elemei

````Fin n```` elemeinek kiolvasása nem olyan nyilvánvaló és transzparens, mint ahogy azt szeretnénk. Tegyünk erre egy kísérletet:

````Fin 0```` olyan típus, aminek nincs lakója. Ezt abból látjuk, hogy a konstruktorok bármilyen bemenetre csak ````Fin S n```` alakú típusba eső lakókat hoznak létre, máshogy meg nem jöhet létre lakó. 

````Fin 1```` egy lakója jön létre, ha fzero-t mondunk, vagy így gondoljuk vagy nyíltan behódolunk vagy elegünk van már az egészből és nem gondolunk semmit (Esterházy Péter, *A szavak csodálatos életéből*) :grin:. Az fsucc konstruktorral nem tudunk Fin 1-beli elemet létrehozni, mert Fin 0-nak nincs eleme és ahhoz ilyet kéne felmutatnunk. 

````Fin 2```` két lakója ````fzero```` és ````fsucc fzero````, ahogy fzero a Fin 1 egyetlen elemeként szerepel. Ha a rejtett paramétert is ki akarjuk írni, akkor a @ szimbólimot használjuk: 
 
````coq
Check @fzero 1 : Fin 2.

Check @fsucc 1 (@fzero 0) : Fin 2.

````

Fin 1-nek, mint véges típusnak szintén van induktora, bár az igaz, hogy Fin 1 egy típuscsaládnak (függő típusnak) eleme és nem önállóan definiált típus. Az induktor az lenne, ami arra enged következtetni, hogy ````P : Fin 1 -> Prop```` egy predikátum mikor igaz a típus összes elemére:

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP%3A%5Cmathrm%7BFin%7D%5C%3B1%5Cto%20%5Cmathrm%7BProp%7D%5Cquad%5Cquad%20f%3AP%5C%3B%5Cmathrm%7Bfzero%7D%7D%7B%5Cforall%20x%3A%20%5Cmathrm%7BFin%7D%5C%3B1%2C%5C%3B%20P%5C%3Bx%7D">

A probléma abban áll, hogy akár hogy is ügyeskedünk, nem kerülhetjük meg, hogy Fin elemeinek rejtett paraméterét (````{n}````) ne szerepeltessük az induktorban. Ennek megfelelően az egyik megoldás egy csak a Fin 1-re jellemző induktor megfogalmazására az, hogy hivatkozunk a teljes típuscsalád indukciós szabályára, aminek a típusa a következő. Minden <img src="https://render.githubusercontent.com/render/math?math=P%3A%5Cprod%20(n%3A%5Cmathrm%7Bnat%7D)%2C%5Cmathrm%7BFin%7D%5C%3Bn%5Cto%20%5Cmathrm%7BProp%7D"> esetén:

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5Cforall%20n%3A%5Cmathrm%7Bnat%7D%2C%20%5C%3BP%20%5C%2C(%5Cmathrm%7BS%7D%5C%2Cn)%20%5C%2C%5Cmathrm%7Bfzero%7D%5Cquad%5C%3B%20%5Cforall%20n%3A%5Cmathrm%7Bnat%7D%2C%20f%3A%5Cmathrm%7BFin%7D%5C%2Cn%2C%20P%5C%2Cn%5C%2C%20f%5C%2C%20%5Cto%5C%2C%20P%5C%2C(%5Cmathrm%7BS%7D%5C%2C%20n)%5C%2C%20(%5Cmathrm%7Bfsucc%7D%5C%2C%20f)%7D%7B%5Cforall%20n%3A%5Cmathrm%7Bnat%7D%2Cx%3A%20%5Cmathrm%7BFin%7D%5C%3Bn%2C%5C%3B%20P%5C%2Cn%5C%2Cx%7D">

Vagy Coq nyelven:

````coq
Fin_ind : forall P : forall n : nat, Fin n -> Prop, 
          (forall n : nat, P (S n)  @fzero n) ->
          (forall (n : nat) (f0 : Fin n), P n f0 -> P (S n) (@fsucc n f0)) ->
          forall (n : nat) (f1 : Fin n), P n f1
````

Érdemes először a Fin 0 induktorát definiálni:

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP%3A%5Cmathrm%7BFin%7D%5C%2C0%5Cto%20%5Cmathrm%7BProp%7D%5Cquad%20p%3A%5Cmathrm%7BFin%7D%5C%2C0%7D%7B%5Cmathrm%7BFin%7D%5C%2C%5Cmathrm%7Bind%7D%5C%2C0%3A%20P%20p%7D">

````coq
Definition Fin_0_ind (P : Fin 0 -> Prop) (p: Fin 0): P p := 
match p with 
  | fzero => (fun x => False_ind IDProp x) 
  | fsucc _ => (fun x => False_ind IDProp x) 
end.
````
Majd készíteni egy olyan ````nat```` bemenetű segédfüggvényt, ami egy adott ````Q : Fin 1 -> Prop```` függvényt ad vissza, ha az a szóban forgó természetes szám az 1 és az azonosan True függvényt, ha a más.

````coq
Definition Aux_Fin_ind_1 (Q : Fin 1 -> Prop) ( n : nat ) : Fin n -> Prop := 
match n with 
  | 0 => fun x : Fin 0 => True
  | 1 => fun x : Fin 1 => Q x
  | S (S m) => fun x : Fin (S (S m)) => True
end.
````
Így Fin 1 induktora menten megvan:
````coq
Definition Fin_1_ind (Q : Fin 1 -> Prop) (f0 : Q fzero) :
 forall (f : Fin 1), Q f.
  apply Fin_ind with (P:= Aux_Fin_ind_1 Q).
  - induction n.
    + exact f0.
    + compute; auto.
  - intros.
    induction n.
    + apply False_ind.
      {apply Fin_0_ind.
      exact f. }
    + compute; auto.
Defined.
````

Vegyük észre, hogy Fin 1-ről nem lehet beszélni az össze konstruktor értékének megadása nélkül. ,,Nincs kettő négy nélkül'', azaz hiába tudjuk, hogy Fin 1 egyetlen eleme fzero, az fsucc ... alakú hipotetikus lakókról is nyilatkoznunk kell. 

Az induktor segítségével be tujduk látni, hogy Fin 1 valóban egyelemű, azaz akárhogy is vesszük egy elemét, az ugyanaz, mint az fzero.

````coq
Definition Fin_1_egyelemu : forall (x:Fin 1), fzero=x := 
Fin_1_ind (fun x => fzero=x) eq_refl.
````

## Fin 2 elemei és az, hogy ő Set-izomorf bool-lal

Világos, hogy ha tovább akarunk menni, akkor definiálnunk kell Fin 2 induktorát. Az ugyan igaz, hogy a Coq automatikusan generálja ezt, de ember legyen a talpán, aki használni képes. Fin 2 induktora tehát a következő induktív jellegű szabály lesz:

````coq
Theorem Fin_2_ind (P : (Fin 2) -> Prop) (f0: P fzero) (f1 : forall f3 : Fin 1, P (fsucc f3) ) : forall (p:Fin 2), P p.
Proof.
  intro p. 
  exact match p with
          | @fzero 1 => f0
          | @fsucc 1 x => f1 x
        end.
  Show Proof.
Defined.
````
Először annak a definíciója, hogy egy függvény kölcsönösen egyértelmű, azaz bijekció: 

````coq
Definition Bijection (A B:Set) (j:A->B) : Prop := 
  (forall y: B, exists x: A, j(x)=y) /\
  forall x1 x2 : A, j(x1)=j(x2) -> x1=x2. 
````

Ez azért kell, mert akkor mondjuk, hogy A és B azonos számosságú, ha van bijekció a két halmaz között. Ez a Fin 2 és bool között a következő (amiről be kell majd látnunk, hogy valóban bijekció).

````coq
Definition f : (Fin 2) -> bool := fun x => 
            match x with 
              | @fzero 1 => true 
              | @fsucc 1 _ => false 
            end.
````
És akkor a releváns bizonyítás.

````coq
Theorem Fin_2_bool : Bijection (Fin 2) bool f.
Proof.
  unfold Bijection.
  split.
  apply bool_ind.
  apply ex_intro with (x:=@fzero 1).
  compute; auto.
  apply ex_intro with (x:=@fsucc 1 (fzero)).
  compute; auto.
  intros x1 x2.
  apply Fin_2_ind with (P:=fun x1 => (f x1 = f x2 -> x1 = x2)).
  simpl.
  apply Fin_2_ind with (P:=fun x2 => (true = f x2 -> fzero = x2)).
  compute; auto.
  intros f3.
  compute.
  intro.
  assert (K:true <> false).
  discriminate.
  contradiction.
  intros f3.
  simpl.
  apply Fin_2_ind with (P:=fun x2 => (false = f x2 -> fsucc f3 = x2)).
  compute.
  intro.
  assert (K: false <> true).
  discriminate.
  contradiction.
  intros f0.
  compute.
  intros.
  assert (K1:fzero=f3).
  apply Fin_1_egyelemu with (x:=f3).
  assert (K2:fzero=f0).
  apply Fin_1_egyelemu with (x:=f0).
  assert (K3: f3=f0).
  congruence. 
  rewrite K3; auto.
Qed.
````

Kicsit körülményes.

Egyszerűbb belátni, hogy Fin 2 kételemű:

````coq
Definition Fin_2_ketelemu : (forall x:Fin 2, x=fzero \/ x=fsucc fzero) /\ (fzero <> (fsucc (@fzero 0))).
  split.
  intros.
  apply Fin_2_ind with (P:=fun x => (x=fzero \/ x=fsucc fzero)).
  left.
  auto.
  intros.
  right.
  enough (H:fzero=f3).
  rewrite H.
  auto.
  apply Fin_1_egyelemu with (x:=f3).
  discriminate.
Defined.
````

A tanult új taktikák: ````assert````, ````contradiction````, ````enough````.

## Egyszerűbb feladatok

1. True egyelemű típus, egyetlen lakója true (SearchAbout True.). Igazoljuk, hogy az f: Fin 1 -> True, fzero |---> true bijekció Fin 1 és True között. Puskázhatunk innen: [https://coq.inria.fr/library/Coq.Vectors.Fin.html].
2.  bFun egy olyan függő típus, mely a többváltozós bool függvényeket fogja össze. 
````coq
Fixpoint bFun (n:nat) : Set :=
  match n with
    | 0 => bool
    | S m => bool -> bFun m
  end.
````
Például andb egy bool->bool->bool függvény és egyben egy bFun 2 típusú függvény is:

````coq
Check andb : bFun 2.
````
nbTree egy olyan típus, ami olyan fákból áll, amiknek akármennyi, de véges sok elágazása lehet, a csúcsokon bool (ennek megfelelő számú bemenetű) műveletek vannak, a leveleken bool értékek.

````coq
Inductive nbTree : Type :=
  | leaf : bool -> nbTree
  | node : forall {n : nat}, bFun n -> (Fin n -> nbTree) ->  nbTree.
````

Például az alábbi egy nbTree fa:

````coq
Definition f (z : Fin 2) :=  
  match z with 
          | fzero  => leaf true
          | fsucc (fzero) => leaf false
          | _ => leaf false
  end.

Check (@node 2) andb f.
````
Mondjunk még 1-2 ilyen fát!

## Nehezebb feladatok

4. Fogalmazzuk meg Fin 0-ra az indukciós szabályt, igazoljuk, hogy Fin 0 nulla elemű és igazoljuk, hogy Fin 0 Set-izomorf False-szal. Puskázhatunk innen: [https://coq.inria.fr/library/Coq.Vectors.Fin.html].
5. Készítsük el azt a transzformációt, ami egy bTree fából egy nbTree fát csinál.

````coq
Inductive bTree : Set :=
  | bleaf : bool -> bTree
  | bnode : (bool->bool->bool) -> bTree -> bTree -> bTree.
````


