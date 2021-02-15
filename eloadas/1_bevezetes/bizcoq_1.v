Print nat.
Print nat_rec.

Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

Print Boole_ind.

Definition Boole_Or (b1:Boole) (b2:Boole) : Boole :=
  match b1 with 
    | igaz => match b2 with 
                | igaz => igaz
                | hamis => igaz 
              end 
    | hamis => match b2 with 
                | igaz => igaz
                | hamis => hamis
              end
  end.

Notation "x 'vagy' y" := (Boole_Or x y) (at level 20) : type_scope.

Check igaz vagy hamis.

Eval compute in (igaz vagy hamis).

SearchAbout nat.

Definition Boole_And (b1 : Boole) (b2: Boole) : Boole := 
  match b1 with 
    | igaz => match b2 with | igaz => igaz | hamis => hamis end
    | hamis => match b2 with | igaz => hamis | hamis => hamis end end.


Notation "x 'es' y" := (Boole_And x y) (at level 20) : type_scope.


Definition Boole_Not (b : Boole) : Boole := 
  match b with 
    | igaz => hamis 
    | hamis => igaz
  end.

Notation "'nem' x" := (Boole_Not x) (at level 20) : type_scope.

Theorem LEM : (forall x : Boole, x vagy (nem x) = igaz). 
Proof.
  intros.
  Print Boole_ind.
  apply Boole_ind with (P:= fun x => x vagy (nem x) = igaz).
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  Show Proof.
Qed.

Theorem DM_1 : (forall x y : Boole, (nem x) vagy (nem y) = nem (x es y) ).
Proof. 
  intros.
  apply Boole_ind with (P:=fun x => (nem x) vagy (nem y) = nem (x es y)).
  apply Boole_ind with (P:=fun y => (nem igaz) vagy (nem y) = nem (igaz es y)).
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  apply Boole_ind with (P:=fun y => (nem hamis) vagy (nem y) = nem (hamis es y)).
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_And.
  unfold Boole_Not.
  reflexivity.
  Show Proof.
Qed. 

SearchAbout bool.




  





