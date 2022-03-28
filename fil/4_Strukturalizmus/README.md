# Menekülés a fundácionalizustól

## Benacerraf kritikája

Paul Benacerraf amellett érvelt, hogy nincs semmi értelme a matematikai objektumokat, pusztán mint tárgyakat definiálni. Csak strukturában lehet őket értelmezni. Ez nagyon közel van Wittgenstein elképzeléséhez nyelvjáték elképzeléséhez. Semmi értelme a "huszár" nevű sakkfigurát az alakja alapján definiálni. A jelentését megadni csak a sakk szabályai alapján lehet. 

Tractatus 1.1 A világ a tények összesség, nem a dolgoké. (W.)

## Komputációs triád

Van itt egy melyebb összefüggés is. A **Curry-Hovard-Lambek tétel** szerint a _konstruktív logika_, a _típusos funkcionális programozás_ és a _kategóraielmélet_ izomorfizmus erelyéig ugyanaz. Azaz a bizonyítások programok és a programok morfizmusok, a morfizmusok bizonyítások.

| <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7Bp%3AA%7D%7B%0Ain_1%20p%3AA%5Cvee%20B%7D%5Cquad%20%5Cdfrac%7Bp%3AB%7D%7B%0Ain_2%20p%3AA%5Cvee%20B%7D"> |  |
| ---- | ---- |  
| <img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7B%5Cbegin%7Bmatrix%7D%20%26%20%5Bp_1%3AA%5D%20%26%20%5Bp_2%3AB%5D%5C%5C%0A%26%20%5Cvdots%20%26%20%5Cvdots%5C%5C%0Ap_3%3AA%5Cvee%20B%20%26%20p_4%3AC%20%26%20p_5%3A%20C%5Cend%7Bmatrix%7D%7D%7Bdis(p_i)%3AC%7D"> |  <img src="https://github.com/mozow01/bizcoq2021/blob/main/coprod.png" width=300>  |

## Mire használhatják a matematikusok: a legjobban illeszkerő alkalmazás a kategórialemélet

````coq

Class Category := cat_mk {
  Obj : Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

  Dom {x y} (f: Hom x y) := x;

  CoDom {x y} (f: Hom x y) := y;

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;

  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;

}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Context {C : Category}.


Class coCartCat := {

(* összeg*)

  Sum_obj : Obj -> Obj -> Obj;

  Sum_mor : forall {x y z} (f:x → z) (g:y → z), Sum_obj x y → z;

  in_1 {x y} : x → (Sum_obj x y);
  in_2 {x y} : y → (Sum_obj x y);

  sum_ax : forall {x y z} (f : x → z) (g : y → z), 
    ((Sum_mor f g) ∘ in_1 = f) /\ ((Sum_mor f g) ∘ in_2 = g);
    
  sum_eq : forall {x y z} (g : Sum_obj x y → z),
    Sum_mor (g ∘ in_1) (g ∘ in_2) = g;
}.

Context {CoC : coCartCat}.

Notation "f '∐' g" := (Sum_mor f g) (at level 40, no associativity) : type_scope.

Theorem unique_sum : forall x y z (f1 : x → z) (f2 : y → z) (g : Sum_obj x y → z),
    ((g ∘ in_1 ) = f1 ) /\ ((g ∘ in_2 ) = f2) ->  f1 ∐ f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply sum_eq.
Qed.


Theorem compos_sum : forall x y z w (f : x → z ) (g : y → z ) (h : z → w),
  ( h ∘ f ) ∐ ( h ∘ g ) = h ∘ ( f ∐ g ).
Proof.
intros.
apply unique_sum.
split.
assert (H: h ∘ (( f ∐ g ) ∘ in_1)  = h ∘ ( f ∐ g ) ∘ in_1).
apply assoc.
rewrite <- H.
assert (K: (f ∐ g) ∘ in_1 =f).
apply sum_ax.
rewrite K.
auto.
assert (H: h ∘ (( f ∐ g ) ∘ in_2)  = h ∘ ( f ∐ g ) ∘ in_2).
apply assoc.
rewrite <- H.
assert (K: (f ∐ g) ∘ in_2 =g).
apply sum_ax.
rewrite K.
auto.
Qed.

Notation "x ⊕ y" := (Sum_obj x y) (at level 40, left associativity) :
type_scope. 

Definition isomorph x y := exists (i : x → y) (j : y → x), i ∘ j = Id y /\ j ∘ i = Id x.

Notation "x '≅' y" := (isomorph x y) (at level 40, left associativity) :
type_scope.

Theorem x_meg_y_egyenlő_y_meg_x : forall X Y, (X ⊕ Y) ≅ (Y ⊕ X).
Proof.
intros.
unfold isomorph. 
exists ((@in_2 CoC Y X) ∐ (@in_1 CoC Y X)).
exists ((@in_2 CoC X Y) ∐ (@in_1 CoC X Y)).
split.
rewrite <- compos_sum.
assert (K: (@in_2 CoC Y X) ∐ (@in_1 CoC Y X) ∘ in_2 = in_1).
apply sum_ax.
rewrite K.
assert (L: (@in_2 CoC Y X) ∐ (@in_1 CoC Y X) ∘ in_1 = in_2).
apply sum_ax.
rewrite L.
apply unique_sum.
rewrite id_2.
split.
auto.
apply id_2.
rewrite <- compos_sum.
assert (K: (@in_2 CoC X Y) ∐ (@in_1 CoC X Y) ∘ in_2 = in_1).
apply sum_ax.
rewrite K.
assert (L: (@in_2 CoC X Y) ∐ (@in_1 CoC X Y) ∘ in_1 = in_2).
apply sum_ax.
rewrite L.
apply unique_sum.
rewrite id_2.
split.
auto.
apply id_2.
Qed.
````




