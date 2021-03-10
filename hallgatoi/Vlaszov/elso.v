Print nat.
Print nat_ind.
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
Theorem LEM : (forall x : Boole, x vagy (nem x) = igaz). 
Proof.
  intros.
  Print Boole_ind.
  apply Boole_ind with (P:= fun x => x vagy (nem x) = igaz).
  unfold Boole_Or.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_Not.
  Show Proof.
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
Definition Boole_imp (b1 : Boole) (b2 : Boole) : Boole :=
  match b1 with
    | igaz => match b2 with | igaz => igaz | hamis => hamis end
    | hamis => igaz
  end.

Notation "'Ha' x 'akkor' y" := (Boole_imp x y) (at level 20) : type_scope.

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

Notation "x 'akkor_es_csak_akkor' y" := (Boole_csa x y) (at level 20) : type_scope.

Theorem ha_akkor : forall x y : Boole, (Boole_imp x y) = ((nem x) vagy y).
  intros.
  apply Boole_ind with (P:= fun x => (Ha x akkor y) = ((nem x) vagy y)).
  apply Boole_ind with (P:= fun y => (Ha igaz akkor y) = ((nem igaz) vagy y)).
  unfold Boole_imp.
  auto.
  auto.
  unfold Boole_Not.
  apply Boole_ind with (P:= fun y => (Ha hamis akkor y) = ((nem hamis) vagy y)).
  auto.
  auto.
  Show Proof.
Qed.

Theorem csak_akkor : forall x y : Boole, Boole_csa (Boole_imp x y) ((nem x) vagy y) = igaz.
  intros.
  apply Boole_ind with (P:= fun x => (Ha x akkor y) akkor_es_csak_akkor ((nem x) vagy y) = igaz).
  apply Boole_ind with (P:= fun y => (Ha igaz akkor y) akkor_es_csak_akkor ((nem igaz) vagy y) = igaz).
  unfold Boole_imp.
  auto.
  auto.
  apply Boole_ind with (P:= fun y => (Ha hamis akkor y) akkor_es_csak_akkor ((nem hamis) vagy y) = igaz).
  auto; auto.
  unfold Boole_imp.
  unfold Boole_Not.
  unfold Boole_Or.
  unfold Boole_csa.
  reflexivity.
  Show Proof.
Qed.

Theorem DM_2 : forall x y : Boole, ((nem x) es (nem y)) = nem (x vagy y).
  intros.
  apply Boole_ind with (P:=fun x => (nem x) es (nem y) = nem (x vagy y)).
  apply Boole_ind with(P:= fun y => (nem igaz) es (nem y) = nem (igaz vagy y)).
  unfold Boole_Or.
  unfold Boole_Not.
  auto.
  unfold Boole_Or.
  unfold Boole_Not.
  auto.
  apply Boole_ind with (P:= fun y => (nem hamis) es (nem y) = nem (hamis vagy y)).
  unfold Boole_Or.
  unfold Boole_Not.
  auto.
  unfold Boole_Or.
  auto.
  Show Proof.
Qed.



