(*STT nyelve implicit változókkal*)

Require Import List.

(*Típusok nyelve*)

Inductive Typ : Set :=
  | Iota : Typ
  | Arrow : Typ -> Typ -> Typ.

Notation "'ι'" := Iota (at level 20).
Infix "→" := Arrow (at level 20, right associativity).

(*Változók: nameless dummies :)

Nincsenek explicit változók, csak indexek, amik azt mondják meg, hogy a kontextus hanyadik eleme az illető implicit 'változó'. *)

(*A kontextusok típusok listái, a művelet a kontextuskibővítés (balról hozzáfűzünk a listához egy új elemet ez a :: )*)

Definition Cntxt := list Typ.

(* Külön vannak kifejezések (terminusok, termek)*)

Inductive Trm : Set :=
  | ind : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.

Notation "x '$' y" := (app x y) (at level 20).

(* Mivel itt bizonyításokról, levezetsekről van szó (és ez szemléletesebb is), ezért an n-edik 
változót 

ind n 

jelöli. Ez viszont nem egy abszolút sorszám, hanem egy relatív.
A Γ = A_0::A_1::A_2::...::nil kontextusban ind 0 pl. az lista első elemére, 
az A_0 típusúváltozóra mutat. Ha Γ bővül egy elemmel, 
a sorrendek eltolódnak 1-gyel. 

lam-nál meg kell jelölni, hogy milyen típusú termet absztrahál, azaz lam egy Typ -> Trm -> Trm típusú lesz.

app problémamentes
*)

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | Ty_ind0 : forall Γ A, Tyty (A :: Γ) (ind 0) A
  | Ty_indS :
      forall Γ A B i,
      Tyty Γ (ind i) A -> Tyty (B :: Γ) (ind (S i)) A
  | Ty_app :
      forall Γ t s A B,
      Tyty Γ t (Arrow A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | Ty_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Arrow A B).

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Lemma First_typeability_rule_for_snd_term : forall (Γ : Cntxt) (A B : Typ), 
A :: B :: Γ ⊢ (ind 1) [:] B.
Proof.
intros.
apply (Ty_indS).
apply (Ty_ind0).
Qed.


Theorem Chain_rule : forall (A B C : Typ), exists (P : Trm), 
A → B :: B → C :: nil ⊢ P [:] A → C.
Proof.
intros.
exists (lam A (app (ind 2) ((app (ind 1) (ind 0)) ))).
apply (Ty_lam).
apply Ty_app with (A:=B) (B:=C).
apply Ty_indS.
apply Ty_indS.
apply Ty_ind0.
apply Ty_app with (A:=A) (B:=B).
apply Ty_indS.
apply Ty_ind0.
apply Ty_ind0.
Qed.
