(* ea *)

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

Definition Boole_Imp (x : Boole) (y: Boole) : Boole := 
  match x with 
    | igaz => match y with
                | igaz => igaz
                | hamis => hamis
              end
    | hamis => match y with
                | igaz => igaz
                | hamis => igaz
              end
  end.

Notation "x 'imp' y" := (Boole_Imp x y) (at level 20) : type_scope.

Definition Boole_Iff (x : Boole) (y: Boole) : Boole := 
  match x with 
    | igaz => match y with
                | igaz => igaz
                | hamis => hamis
              end
    | hamis => match y with
                | igaz => hamis
                | hamis => igaz
              end
  end.

Notation "x 'acsa' y" := (Boole_Iff x y) (at level 20) : type_scope.


(* hf 1 *)

Theorem hf_1a : (forall x y : Boole, (x imp y) = ((nem x) vagy y)).
Proof. 
  intros.
  apply Boole_ind with (P:=fun x => (x imp y) = ((nem x) vagy y)).
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

Theorem hf_1b : (forall x y : Boole, (x imp y) acsa ((nem x) vagy y) = igaz).
Proof. 
  intros.
  apply Boole_ind with (P:=fun x => (x imp y) acsa ((nem x) vagy y) = igaz).
  apply Boole_ind with (P:=fun y => (igaz imp y) acsa ((nem igaz) vagy y) = igaz).
  unfold Boole_Iff.
  unfold Boole_Not.
  unfold Boole_Imp.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Iff.
  unfold Boole_Not.
  unfold Boole_Imp.
  unfold Boole_Or.
  reflexivity.
  apply Boole_ind with (P:=fun y => (hamis imp y) acsa ((nem hamis) vagy y) = igaz).
  unfold Boole_Iff.
  unfold Boole_Not.
  unfold Boole_Imp.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Iff.
  unfold Boole_Not.
  unfold Boole_Imp.
  unfold Boole_Or.
  reflexivity.
  Show Proof.
Qed.


(* hf 2 *)

Theorem hf_2 : (forall x y : Boole, ((nem x) es (nem y)) = nem (x vagy y)).
Proof. 
  intros.
  apply Boole_ind with (P:=fun x => ((nem x) es (nem y)) = nem (x vagy y)).
  apply Boole_ind with (P:=fun y => (nem igaz) es (nem y) = nem (igaz vagy y)).
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  unfold Boole_Not.
  unfold Boole_And.
  unfold Boole_Or.
  reflexivity.
  apply Boole_ind with (P:=fun y => (nem hamis) es (nem y) = nem (hamis vagy y)).
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
