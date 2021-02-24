Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

Definition Boole_Or (b1: Boole) (b2: Boole) : Boole := 
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

Definition Boole_And (b1 : Boole) (b2: Boole) : Boole := 
  match b1 with 
    | igaz => match b2 with | igaz => igaz | hamis => hamis end
    | hamis => match b2 with | igaz => hamis | hamis => hamis end 
    end.

Notation "x 'es' y" := (Boole_And x y) (at level 20) : type_scope.


Definition Boole_Not (b : Boole) : Boole := 
  match b with 
    | igaz => hamis 
    | hamis => igaz
  end.

Notation "'nem' x" := (Boole_Not x) (at level 20) : type_scope.

Definition Boole_Imp (b1:Boole) (b2:Boole) : Boole :=
    match b1 with 
    | igaz => match b2 with 
                | igaz => igaz 
                | hamis => hamis
              end
    | hamis => match b2 with 
                | igaz => igaz 
                | hamis => igaz
               end
end.

Notation "x 'implikalja' y" := (Boole_Imp x y) (at level 20) : type_scope.

Definition Boole_Iff (b1:Boole) (b2:Boole) : Boole :=
    match b1 with 
    | igaz => match b2 with 
                | igaz => igaz 
                | hamis => hamis
              end
    | hamis => match b2 with 
                | igaz => hamis 
                | hamis => igaz
               end
end.

Notation "x 'iff' y" := (Boole_Iff x y) (at level 20) : type_scope.



Theorem gyak1 : (forall x y : Boole, (x implikalja y) = ((nem x) vagy y)).
Proof.
  intros.
  apply Boole_ind with (P:= fun x => (x implikalja y) = ((nem x) vagy y)).
  apply Boole_ind with (P:= fun y => (igaz implikalja y) = ((nem igaz) vagy y)).
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  apply Boole_ind with (P:= fun y => (hamis implikalja y) = ((nem hamis) vagy y)).
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  Show Proof.
Qed.

Theorem gyak2 : (forall x y : Boole, (x implikalja y) iff ((nem x) vagy y) = igaz ).
Proof.
  intros.
  apply Boole_ind with (P:= fun x => (x implikalja y) iff ((nem x) vagy y) = igaz).
  apply Boole_ind with (P:= fun y => (igaz implikalja y) iff ((nem igaz) vagy y) = igaz).
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_Iff.
  reflexivity.
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_Iff.
  reflexivity.
  apply Boole_ind with (P:= fun y => (hamis implikalja y) iff ((nem hamis) vagy y) = igaz).
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_Iff.
  reflexivity.
  unfold Boole_Imp.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_Iff.
  reflexivity.
  Show Proof.
Qed.

Theorem gyak3 : ( forall x y : Boole, ((nem x) es (nem y)) = nem (x vagy y) ).
Proof.
  intros.
  apply Boole_ind with (P:= fun x => ((nem x) es (nem y)) = nem (x vagy y) ).
  apply Boole_ind with (P:= fun y => ((nem igaz) es (nem y)) = nem (igaz vagy y) ).
  unfold Boole_Or.
  unfold Boole_Not.
  unfold Boole_And.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_Not.
  unfold Boole_And.
  reflexivity.
  apply Boole_ind with (P:= fun y => ((nem hamis) es (nem y)) = nem (hamis vagy y) ).
  unfold Boole_Or.
  unfold Boole_Not.
  unfold Boole_And.
  reflexivity.
  unfold Boole_Or.
  unfold Boole_Not.
  unfold Boole_And.
  reflexivity.
Qed.



