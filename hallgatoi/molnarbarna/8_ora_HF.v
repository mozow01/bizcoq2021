Reserved Notation "A 'wimp' B" (at level 99).

Inductive WImp (A B : Prop) : Prop :=
  | wl : ~A -> A wimp B
  | wr : ~~B -> A wimp B
where "A 'wimp' B" := (WImp A B) : type_scope.

Print WImp_ind.


Theorem problem_1 : forall A B : Prop, A wimp B -> A -> ~~B.
Proof.
  intro.
  intro.
  intro.
  induction H. contradiction.
  auto.
Qed.




Theorem problem_2 : forall A B C: Prop, 
A -> A wimp (B wimp C) -> (~~(B wimp C)) wimp C -> ~~C.
Proof.
  intro.
  intro.
  intro.
  intros.
  destruct H0.
  contradiction.
  destruct H1.
  contradiction.
  auto.
Qed.



Axiom wmp : forall A B : Prop, A wimp B -> A -> ~~B.

Theorem wimp_ind : forall A B P : Prop, (A \/ ~A) -> (~ A -> P) -> (~ ~ B -> P) -> (A wimp B) -> P.
Proof.
  intro.
  intro.
  intro.
  intro.
  intro.
  intro.
  intro.
  Print wmp.
  destruct H2.
  auto.
  auto.
Qed.
