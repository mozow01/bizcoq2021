(* ea *)

Structure Group : Type := const_kozos
{
  A :> Set;

  op : A -> A -> A ;
  inv : A -> A ;
  z : A ;

  op_assoc : forall a b c, op a (op b c) = op (op a b) c;
  op_z : forall a, op a z = a /\ op z a = a ;
  op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
}.


(* hf *)

Fixpoint iter {A:Set} (k:nat) (f:A->A) (x:A) :=
  match k with
    | 0 => x
    | S p => iter p f (f x)
  end.

Eval compute in Nat.add 0 1.

Eval compute in iter 0 (Nat.add 1) 0.
Eval compute in iter 1 (Nat.add 1) 0.
Eval compute in iter 2 (Nat.add 1) 0.

Structure CyclicGroup : Type := const_cyclic (* motto *)
{
  G :> Group;

  generator : A G ;
  n : nat ;

  op_cyclic : forall a, exists k, k < n /\ a = iter k ((op G) generator) (z G)
}.

Inductive GeneratedElement : Set :=
  | g : nat -> GeneratedElement.

Check g 0.
Check g 1.

Definition order (e:GeneratedElement) : nat := match e with | g k => k end.

Eval compute in order (g 0).
Eval compute in order (g 1).


Definition Z_n (n:nat) := {e:GeneratedElement | order e < n}.

Lemma g_0_order_lt_2 : order (g 0) < 2.
Proof.
  unfold order.
  auto.
Qed.

Definition z_2_0 := exist (fun e:GeneratedElement => order e < 2) (g 0) g_0_order_lt_2.

Eval compute in proj1_sig z_2_0.
Eval compute in proj2_sig z_2_0.

Search proj1_sig.
Search proj2_sig.
Check eq_sig.


Definition Z_n_order (n:nat) (z:Z_n n) : nat := order (proj1_sig z).

Eval compute in Z_n_order 2 z_2_0. 


Lemma g_k_order_lt_n (n:nat) (k:nat) : k < n -> order (g k) < n. Proof. unfold order. auto. Qed.

Definition Z_n_const (n:nat) (k:nat) (p:k < n): Z_n n :=
  exist (fun e:GeneratedElement => order e < n) (g k) (g_k_order_lt_n n k p).

Lemma proof_0_lt_1 : 0 < 1. Proof. auto. Qed. (* FIXME: create by function; possible? *)
Lemma proof_0_lt_2 : 0 < 2. Proof. auto. Qed.
Lemma proof_1_lt_2 : 1 < 2. Proof. auto. Qed.
Lemma proof_0_lt_3 : 0 < 3. Proof. auto. Qed.
Lemma proof_1_lt_3 : 1 < 3. Proof. auto. Qed.
Lemma proof_2_lt_3 : 2 < 3. Proof. auto. Qed.

Definition z_3_0 := Z_n_const 3 0 proof_0_lt_3.
Definition z_3_1 := Z_n_const 3 1 proof_1_lt_3.
Definition z_3_2 := Z_n_const 3 2 proof_2_lt_3.

Eval compute in Z_n_order 3 z_3_0.
Eval compute in Z_n_order 3 z_3_1.
Eval compute in Z_n_order 3 z_3_2. 

Lemma Z_n_order_lt_n (n:nat) : forall x:Z_n n, Z_n_order n x < n.
Proof.
  intro x.
  unfold Z_n_order.
  apply (proj2_sig x).
Qed.


SearchPattern (nat -> nat -> nat).
Print Nat.modulo.

Notation "n % m" := (Nat.modulo n m) (at level 20) : type_scope.

Eval compute in 0 % 0.
Eval compute in 1 % 2.
Eval compute in 2 % 2. 

Require PeanoNat.

Lemma Z_n_op_proof (n:nat) : forall x y:Z_n n, ((Z_n_order n x) + (Z_n_order n y)) % (n) < (n).
Proof.
  induction x, y.
  unfold Z_n_order.
  apply PeanoNat.Nat.mod_upper_bound.
  cut (n > 0).
  apply PeanoNat.Nat.neq_0_lt_0.
  apply PeanoNat.Nat.lt_lt_0 in p.
  assumption.
Qed.

Definition Z_n_op (n:nat) (x:Z_n n) (y:Z_n n) : Z_n n :=
  Z_n_const n (((Z_n_order n x) + (Z_n_order n y)) % (n)) (Z_n_op_proof n x y).

Eval compute in Z_n_order 3 (Z_n_op 3 z_3_0 z_3_0).
Eval compute in Z_n_order 3 (Z_n_op 3 z_3_0 z_3_1).
Eval compute in Z_n_order 3 (Z_n_op 3 z_3_1 z_3_2).


Lemma Z_n_inv_proof (n:nat) : forall x:Z_n n, (n - (Z_n_order n x)) % (n) < (n).
Proof.
  induction x.
  unfold Z_n_order.
  apply PeanoNat.Nat.mod_upper_bound.
  cut (n > 0).
  apply PeanoNat.Nat.neq_0_lt_0.
  apply PeanoNat.Nat.lt_lt_0 in p.
  assumption.
Qed.

Definition Z_n_inv (n:nat) (x:Z_n n) : Z_n n :=
  Z_n_const n ((n - (Z_n_order n x)) % (n)) (Z_n_inv_proof n x).

Eval compute in Z_n_order 3 (Z_n_inv 3 z_3_0).
Eval compute in Z_n_order 3 (Z_n_inv 3 z_3_1).
Eval compute in Z_n_order 3 (Z_n_inv 3 z_3_2). 

Axiom proof_irrelevance : (* https://github.com/coq/coq/wiki/CoqAndAxioms *)
  forall (P : Prop) (p q : P), p = q.

Lemma warmup (n:nat) (x y:{k:nat | k < n}) : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x Hx], y as [y Hy].
  simpl.
  intro H.
  subst y.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma Z_n_eq_if_order_eq (n:nat) : forall x y:Z_n n, Z_n_order n x = Z_n_order n y -> x = y.
Proof.
  intros x y.
  destruct x as [x Hx], y as [y Hy].
  unfold Z_n_order.
  simpl.
  intro H.
  assert (order x = order y -> x = y) as H2.
  { case x, y. unfold order. intro H2. rewrite H2. reflexivity. }
  assert (x = y).
  apply H2.
  assumption.
  subst y.
  cut (Hx = Hy).
  intro H3.
  rewrite H3.
  reflexivity.
  apply proof_irrelevance.
Qed.

Lemma Z_n_eq_iff_order_eq (n:nat) : forall x y:Z_n n, x = y <-> Z_n_order n x = Z_n_order n y.
Proof.
  split.
  intro H.
  rewrite H.
  reflexivity.
  apply Z_n_eq_if_order_eq.
Qed.


Lemma nat_add_mod_assoc : forall a b c n:nat, n <> 0 -> 
  (a + ((b + c) % (n))) % (n) = (((a + b) % (n)) + c) % (n).
Proof.
  Print PeanoNat.Nat.add_mod.
  Print PeanoNat.Nat.add_mod_idemp_l.
  Print PeanoNat.Nat.add_mod_idemp_r.
  intros a b c n H.
  rewrite PeanoNat.Nat.add_mod_idemp_r.
  rewrite PeanoNat.Nat.add_mod_idemp_l.
  rewrite PeanoNat.Nat.add_assoc.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma Z_n_op_eq_order (n:nat) :
  forall x y:Z_n n, Z_n_order n (Z_n_op n x y) = (((Z_n_order n x) + (Z_n_order n y)) % (n)).
Proof.
  intros x y.
  unfold Z_n_op.
  unfold Z_n_order.
  simpl.
  reflexivity.
Qed.

Lemma Z_n_inv_eq_order (n:nat) :
  forall x:Z_n n, Z_n_order n (Z_n_inv n x) = ((n) - Z_n_order n x) % (n).
Proof.
  intro x.
  unfold Z_n_inv.
  unfold Z_n_order.
  simpl.
  reflexivity.
Qed.


Theorem Z_n_group (n:nat) : n <> 0 -> Group.
Proof.
  intro H.
  assert (0 < n) as H'.
  apply PeanoNat.Nat.neq_0_lt_0.
  assumption.
  apply (const_kozos (Z_n n) (Z_n_op n) (Z_n_inv n) (Z_n_const n 0 H')).

  intros a b c.
  rewrite Z_n_eq_iff_order_eq.
  repeat rewrite Z_n_op_eq_order.
  apply nat_add_mod_assoc.
  assumption.

  intro a.
  repeat rewrite Z_n_eq_iff_order_eq.
  repeat rewrite Z_n_op_eq_order.
  assert (Z_n_order n (Z_n_const n 0 H') = 0) as H2.
  unfold Z_n_order.
  simpl.
  reflexivity.
  rewrite H2.
  rewrite PeanoNat.Nat.add_0_r.
  rewrite PeanoNat.Nat.add_0_l.
  split.
  apply PeanoNat.Nat.mod_small.
  apply Z_n_order_lt_n.
  apply PeanoNat.Nat.mod_small.
  apply Z_n_order_lt_n.

  intro a.
  repeat rewrite Z_n_eq_iff_order_eq.
  repeat rewrite Z_n_op_eq_order.
  assert (Z_n_order n (Z_n_const n 0 H') = 0) as H2.
  unfold Z_n_order.
  simpl.
  reflexivity.
  rewrite H2.

  rewrite Z_n_inv_eq_order.
  split.

  rewrite PeanoNat.Nat.add_mod_idemp_r.
  rewrite PeanoNat.Nat.add_sub_assoc.
  rewrite PeanoNat.Nat.add_sub_swap.
  rewrite PeanoNat.Nat.add_comm.
  rewrite PeanoNat.Nat.add_sub_assoc.
  rewrite PeanoNat.Nat.add_sub.
  apply PeanoNat.Nat.mod_same.
  assumption.
  apply le_n.
  apply le_n.
  assert (Z_n_order n a < n).
  apply Z_n_order_lt_n.
  apply PeanoNat.Nat.lt_le_incl.
  assumption.
  assumption.

  rewrite PeanoNat.Nat.add_mod_idemp_l.
  rewrite PeanoNat.Nat.sub_add.
  apply PeanoNat.Nat.mod_same.
  assumption.
  assert (Z_n_order n a < n).
  apply Z_n_order_lt_n.
  apply PeanoNat.Nat.lt_le_incl.
  assumption.
  assumption.
Qed.

Lemma test (n:nat) (H:n <> 0) : forall a:A (Z_n_group n H), a = a.
Proof.
  intro a.
  (* case a. *)
  reflexivity.
Qed.

(* Lemma test (n:nat) (H:n <> 0) : forall a:A (Z_n_group n H), Z_n_order n a < n. *)

Theorem Z_n_cyclic_group (n:nat) : n > 1 -> CyclicGroup.
Proof.
  intro H.
  assert (n <> 0) as H2.
  assert (n > 0) as H2'.
  apply PeanoNat.Nat.lt_trans with (p:=n) (m:=1) (n:=0).
  apply PeanoNat.Nat.lt_succ_diag_r.
  assumption.
  apply PeanoNat.Nat.neq_0_lt_0.
  assumption.
  Check (Z_n_const n 1 H).
  Check (z (Z_n_group n H2)).
  apply (const_cyclic (Z_n_group n H2) (Z_n_const n 1 H) n).
???
