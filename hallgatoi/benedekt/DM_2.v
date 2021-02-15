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

Theorem DM_2 : (forall x y : Boole, (nem x) es (nem y) = nem (x vagy y)).
Proof.
  intros.
  Print Boole_ind.
  apply Boole_ind with (P:=fun x => (nem x) es (nem y) = nem (x vagy y)).
  apply Boole_ind with (P:=fun y => (nem igaz) es (nem y) = nem (igaz vagy y)).
  unfold Boole_And.
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  auto.
  apply Boole_ind with (P:=fun y=> (nem hamis) es (nem y) = nem (hamis vagy y)).
  unfold Boole_And.
  unfold Boole_Or.
  unfold Boole_Not.
  reflexivity.
  auto.
Qed.
