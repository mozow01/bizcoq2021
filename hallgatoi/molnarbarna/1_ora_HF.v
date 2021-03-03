Print nat.
Print nat_ind.
Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.
Print Boole_ind.

Definition Boole_Or (b1 : Boole) (b2 : Boole) : Boole :=
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
Search nat.
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

Definition Boole_imp (b1 : Boole) (b2 : Boole) : Boole :=
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
Definition Boole_csa (b1 : Boole) (b2 : Boole) : Boole :=
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
Eval compute in (Boole_csa hamis igaz ).
Theorem impli : (forall x y : Boole, (Boole_imp x y) = ((nem x) vagy y)).
Proof.
intros.
apply Boole_ind with (P:= fun x => (Boole_imp x y) = ((nem x) vagy y)).
apply Boole_ind with (P:= fun y => (Boole_imp igaz y) = ((nem igaz) vagy y)).
unfold Boole_imp.
unfold Boole_Or.
reflexivity.
unfold Boole_imp.
unfold Boole_Or.
reflexivity.
unfold Boole_imp.
unfold Boole_Or.
reflexivity.
Show Proof.
Qed.

Theorem hf2 : (forall x y : Boole, Boole_csa (Boole_imp x y) ((nem x) vagy y) = igaz).
Proof.
  intros.
  apply Boole_ind with (P:= fun x => Boole_csa (Boole_imp x y) ((nem x) vagy y) = igaz).
  apply Boole_ind with (P:= fun y => Boole_csa (Boole_imp igaz y) ((nem igaz) vagy y) = igaz).
  unfold Boole_csa.
  unfold Boole_imp.
  reflexivity.
  unfold Boole_csa.
  unfold Boole_imp.
  reflexivity.
  apply Boole_ind with (P:= fun y => Boole_csa (Boole_imp hamis y) ((nem hamis) vagy y) = igaz).
  unfold Boole_csa.
  unfold Boole_imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_csa.
  unfold Boole_imp.
  unfold Boole_Not.
  unfold Boole_Or.
  reflexivity.
  Show Proof.
Qed.

Theorem masik_DE : (forall x y : Boole, ((nem x) es (nem y)) = nem (x vagy y)).
Proof.
  intros.
  apply Boole_ind with (P:= fun x => ((nem x) es (nem y)) = nem (x vagy y)).
  apply Boole_ind with (P:= fun y => ((nem igaz) es (nem y)) = nem (igaz vagy y)).
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  apply Boole_ind with (P:= fun y => ((nem hamis) es (nem y)) = nem (hamis vagy y)).
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  Show Proof.
Qed.

Search bool.

Definition f_1 (g : bool -> bool) : bool :=
  andb (g(true)) (g(false)).

Eval compute in f_1(fun x : bool => orb x (negb x)).





Definition f_1 (g : bool -> bool) : bool :=
  andb (g(true)) (g(false)).

Eval compute in f_1(fun x : bool => orb x (negb x)).

Definition f_2 (g : bool -> bool -> bool) : bool :=
  andb (f_1(g(true))) (f_1(g(false))).

Eval compute in (f_2(fun x : bool => orb x y)).





















