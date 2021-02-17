Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

Definition Boole_And (b1 : Boole) (b2: Boole) : Boole := 
  match b1 with 
    | igaz => match b2 with | igaz => igaz | hamis => hamis end
    | hamis => match b2 with | igaz => hamis | hamis => hamis end end.

Notation "x 'es' y" := (Boole_And x y) (at level 20) : type_scope.

Print sig.

Theorem And_thm : (forall (x y : Boole), { z: Boole | (x es y) = z /\ 
forall (w: Boole), ( (x es y) = w -> z=w)}).
Proof.
  intros.
  Print sig.
  apply exist with (x:=(x es y)).
  split.
  reflexivity.
  intros.
  auto.
  Show Proof.
Defined. 

Definition sig_proj1 (A:Set) (P:A -> Prop) (x : sig P) : A :=
    match x with exist _ a _ => a end.

Definition sig_proj2 (A:Set) (P:A -> Prop) (x : sig P) : P(sig_proj1 A P x) :=
    match x with exist _ _ p => p end. 

Definition And_output (x y : Boole) := sig_proj1 Boole (fun z : Boole => ((x es y) = z /\ 
forall (w: Boole), ( (x es y) = w -> z=w))) (And_thm x y).

Definition And_proof (x y : Boole) := sig_proj2 Boole (fun z : Boole => ((x es y) = z /\ 
forall (w: Boole), ( (x es y) = w -> z=w))) (And_thm x y).

Eval compute in (And_output igaz hamis).

Eval compute in (And_proof igaz hamis).



