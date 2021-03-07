# Absztrakt véges típus

Szükséges lehet, és Coq-ban implementálni is lehet, egy olyan függő típust, ami minden egyes *n* természetes számhoz hozzárendel egy ,,sztenderd'' *n* elemű véges típust. Például ez akkor jó, ha hivatkozni szereténk az összes véges típusra vagy szeretnénk korlátlan, de véges argumentumszámú függvényt vagy ennyi elágazásos fát. Ez a konstrukció a **Fin:**

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

Fin 1-nek, mint véges típusnak szintén van induktora: 

````coq
Theorem Fin_1_ind (P : (Fin 1) -> Prop) (f: P fzero) : forall (p:Fin 1), P p.
Proof.
  intro p.
  exact match p with
          | @fzero 0 => f
          | @fsucc 0 x => (fun (p:Fin 0) => match p with end) x
        end.
  Show Proof.
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