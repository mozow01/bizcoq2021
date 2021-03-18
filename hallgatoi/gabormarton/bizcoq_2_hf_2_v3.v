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

Inductive Fin : nat -> Set :=
  | fzero : forall {p:nat}, Fin (S p)
  | fsucc : forall {p:nat}, Fin p -> Fin (S p).

Check @fzero 0.
Check @fzero 1.
Check @fsucc 1 (@fzero 0).
Check @fzero 2.
Check @fsucc 2 (@fzero 1).
Check @fsucc 2 (@fsucc 1 (@fzero 0)).

Lemma Fin_0_all_v1 : forall (P:Fin 0 -> Prop) (x:Fin 0), P x.
Proof.
  intros P x.
  exact match x as x' return P x with  (* TODO: understand *)
          | @fzero _ => match x with end
          | @fsucc _ _ => match x with end
        end.
Qed.


(* cf. https://coq.inria.fr/library/Coq.Vectors.Fin.html: case0, rectS *) (* TODO: understand *)

Definition Fin_0_all (P:Fin 0 -> Type) (x: Fin 0): P x :=
  match x with | fzero | fsucc _ => fun devil => False_rect (@IDProp) devil end.

Definition Fin_ind_succ (P:forall {p:nat}, Fin (S p) -> Type) (Pz: forall p, @P p fzero)
  (Ps : forall {p:nat} (x:Fin (S p)), P x -> P (fsucc x)) : forall {p:nat} (x: Fin (S p)), P x :=
  fix Fin_ind_succ_fix {p:nat} (x: Fin (S p)): P x :=
    match x with
      | @fzero q => Pz q
      | @fsucc 0 y => Fin_0_all (fun f => P (fsucc f)) y
      | @fsucc (S k) y => Ps y (Fin_ind_succ_fix y)
    end.

Lemma Fin_ind_succ_test : forall (p:nat) (x:Fin (S p)), x = fzero \/ exists y, x = fsucc y.
Proof.
  apply Fin_ind_succ with (P:=fun p x => x = fzero \/ exists y, x = fsucc y).
  intro p.
  left.
  reflexivity.
  intros p x IH.
  destruct IH as [IH1 | IH2].
  right.
  exists x.
  reflexivity.
  destruct IH2 as [y IH2'].
  right.
  exists x.
  reflexivity.
Qed.

Definition Fin_cases := Fin_ind_succ_test.

Lemma Fin_1_all_fzero : forall (x:Fin 1), x = fzero.
Proof.
  intro x.
  assert (x = fzero \/ exists y, x = fsucc y) as L.
  apply Fin_cases.
  destruct L as [L1 | L2].
  assumption.
  destruct L2 as [y L2'].
  assert (x <> fsucc y) as L3.
  apply Fin_0_all with (P:=fun y => x <> fsucc y).
  contradiction.
Qed.


(* cf. https://coq.inria.fr/library/Coq.Vectors.Fin.html: FS_inj *) (* TODO: understand *)

Definition Fin_fsucc_inj_magic {n:nat} (x y:Fin n) (eq: fsucc x = fsucc y) : x = y :=
  match eq in _ = a return
    match a as a' in Fin m return match m with | 0 => Prop | S n' => Fin n' -> Prop end with
      | fzero => fun _ => True
      | fsucc y => fun x' => x' = y
    end x
  with
    eq_refl => eq_refl
  end.

Lemma Fin_fsucc_inj : forall {n:nat} (x y:Fin n), fsucc x = fsucc y -> x = y.
Proof.
  intros n x y.
  apply Fin_fsucc_inj_magic.
Qed.

(*
  let z := @fzero in let s := @fsucc in

  Fin 4: (z 3)   (s 3 (z 2))   (s 3 (s 2 (z 1)))   (s 3 (s 2 (s 1 (z 0))))
                 ^             ^                   ^
                /             /                   /
               / s 3         / s 3               / s 3
              /             /                   /
  Fin 3: (z 2)   (s 2 (z 1))   (s 2 (s 1 (z 0)))
                 ^             ^
                /             /
               / s 2         / s 2
              /             /
  Fin 2: (z 1)   (s 1 (z 0))
                 ^
                /
               / s 1
              /
  Fin 1: (z 0)
  Fin 0: -
*)

Fixpoint succ {n:nat} (x:Fin n) : Fin n := (* n not used :( *)
  match x with
    | @fzero 0 => @fzero 0
    | @fzero (S q) => @fsucc (S q) (@fzero q)
    | @fsucc (S q) y => let s := succ y in match s return Fin (S (S q)) with
                                            | @fzero r => @fzero (S q)
                                            | @fsucc r z => @fsucc (S q) s
                                          end 
    | @fsucc 0 y => match y with end
  end.

Eval compute in succ (@fzero 0).
Eval compute in succ (@fzero 1).
Eval compute in succ (@fsucc 1 (@fzero 0)).
Eval compute in succ (@fzero 2).
Eval compute in succ (@fsucc 2 (@fzero 1)).
Eval compute in succ (@fsucc 2 (@fsucc 1 (@fzero 0))).
Eval compute in succ (@fzero 3).
Eval compute in succ (@fsucc 3 (@fzero 2)).
Eval compute in succ (@fsucc 3 (@fsucc 2 (@fzero 1))).
Eval compute in succ (@fsucc 3 (@fsucc 2 (@fsucc 1 (@fzero 0)))).

Fixpoint iter {A:Set} (n:nat) (f:A->A) (x:A) :=
  match n with
    | 0 => x
    | S p => f (iter p f x)
  end.

Eval compute in Nat.add 0 1.

Eval compute in iter 0 (Nat.add 1) 0.
Eval compute in iter 1 (Nat.add 1) 0.
Eval compute in iter 2 (Nat.add 1) 0.


Definition Z_n (n:nat) := Fin n.

Definition z_1_0 := @fzero 0.
Definition z_2_0 := @fzero 1.
Definition z_2_1 := @fsucc 1 (@fzero 0).
Definition z_3_0 := @fzero 2.
Definition z_3_1 := @fsucc 2 (@fzero 1).
Definition z_3_2 := @fsucc 2 (@fsucc 1 (@fzero 0)).


Fixpoint label {n:nat} (x:Z_n n) : nat := (* n not used :( *)
  match x with
    | @fzero _ => 0
    | @fsucc (S q) y => S (@label (S q) y)
    | @fsucc 0 y => match y with end
  end.

Eval compute in label z_1_0.
Eval compute in label z_2_0.
Eval compute in label z_2_1.
Eval compute in label z_3_0.
Eval compute in label z_3_1.
Eval compute in label z_3_2.

Definition Z_n_op {p:nat} (x:Z_n (S p)) (y:Z_n (S p)) : Z_n (S p) := iter (label y) succ x.

Eval compute in Z_n_op z_3_0 z_3_0.
Eval compute in Z_n_op z_3_0 z_3_1.
Eval compute in Z_n_op z_3_1 z_3_2.

Definition Z_n_inv {p:nat} (x:Z_n (S p)) : Z_n (S p) := iter ((S p) - label x) succ (@fzero p).

Eval compute in Z_n_inv z_3_0.
Eval compute in Z_n_inv z_3_1.
Eval compute in Z_n_inv z_3_2. 


Lemma iter_succ {A:Set} : forall (p:nat) (f:A->A) (x:A), iter (S p) f x = f (iter p f x).
Proof.
  intros p f x.
  case p.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma Z_n_label_fzero : forall {p:nat}, label (@fzero p) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma Z_n_label_fsucc : forall {p:nat} (x:Z_n (S p)), label (fsucc x) = S (label x).
Proof.
  apply Fin_ind_succ with (P:=fun p x => label (fsucc x) = S (label x)).
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Definition Z_n_label_last_pred {p:nat} (x:Z_n (S p)) := succ x = fzero -> label x = p.

Lemma Z_n_label_last : forall {p:nat} (x:Z_n (S p)), Z_n_label_last_pred x. (* not working in-line *)
Proof.
  apply Fin_ind_succ with (P:=fun p x => Z_n_label_last_pred x).
  unfold Z_n_label_last_pred.
  destruct p.
  simpl.
  reflexivity.
  simpl.
  discriminate.
  unfold Z_n_label_last_pred.
  intros p x IH.
  assert (succ x = fzero <-> succ (fsucc x) = fzero) as L. {
    split.
    simpl.
    intro H.
    rewrite H.
    reflexivity.

    simpl.
    intro H.
    assert (succ x = fzero \/ exists y, succ x = fsucc y) as H3.
    apply Fin_cases.
    destruct H3 as [H3_1 | H3_2].
    assumption.
    destruct H3_2 as [y H3_2].
    rewrite H3_2 in H.
    assert (fsucc (fsucc y) <> fzero) as T.
    discriminate.
    contradiction.
  }
  intro H.
  assert (succ x = fzero) as H2.
  apply L.
  assumption.
  rewrite Z_n_label_fsucc.
  rewrite IH.
  reflexivity.
  assumption.
Qed.

Require Import Lia. (* Omega deprecated *) 

Definition Z_n_label_before_last_pred {p:nat} (x:Z_n (S p)) :=
  (exists y, succ x = fsucc y) -> label x < p.

Lemma Z_n_label_before_last : forall {p:nat} (x:Z_n (S p)), Z_n_label_before_last_pred x.
Proof.
  apply Fin_ind_succ with (P:=fun p x => Z_n_label_before_last_pred x). (* not working in-line *)
  unfold Z_n_label_before_last_pred.
  destruct p.
  intro Abs.
  destruct Abs as [y Abs].
  assert (succ fzero <> fsucc y) as Abs2.
  apply Fin_0_all with (P:=fun x => succ fzero <> fsucc x).
  contradiction.
  intro H.
  rewrite Z_n_label_fzero.
  lia.
  unfold Z_n_label_before_last_pred.
  intros p x IH H.
  simpl.
  destruct H as [y H].
  assert ((exists y, succ x = fsucc y) <-> exists y, succ (fsucc x) = fsucc y) as L. {
    split.
    simpl.
    intro H2.
    destruct H2 as [z H2].
    rewrite H2.
    exists (fsucc z).
    reflexivity.
    simpl.
    intro H2.
    destruct H2 as [z H2].
    assert (succ x = fzero \/ exists y, succ x = fsucc y) as H3.
    apply Fin_cases.
    destruct H3 as [H3_1 | H3_2].
    rewrite H3_1 in H2.
    rename H2 into Abs.
    assert (fzero <> fsucc z) as T.
    discriminate.
    contradiction.
    destruct H3_2 as [w H3_2].
    exists w.
    assumption.
  }
  assert (exists y, succ (fsucc x) = fsucc y) as H2.
  exists y.
  assumption.
  assert (exists y, succ x = fsucc y) as H3.
  apply L.
  assumption.
  assert (label x < p) as H4.
  apply IH.
  assumption.
  lia.
Qed.

Lemma Z_n_label_bounded : forall {p:nat} (x:Z_n (S p)), label x < S p.
Proof.
  intros p x.
  assert (succ x = fzero \/ exists y, succ x = fsucc y) as H.
  apply Fin_cases.
  destruct H as [H1 | H2].
  assert (label x = p) as H2.
  apply Z_n_label_last.
  assumption.
  rewrite H2.
  lia.
  assert (label x < p) as H3.
  apply Z_n_label_before_last.
  assumption.
  rewrite H3.
  lia.
Qed.

Lemma Z_n_label_inj : forall {p:nat} (x y:Z_n (S p)), label x = label y -> x = y.
Proof.
  intros p x y.
  induction p.
  assert (x = fzero) as Hx. { apply Fin_1_all_fzero. }
  assert (y = fzero) as Hy. { apply Fin_1_all_fzero. }
  rewrite Hx.
  rewrite Hy.
  reflexivity.
  assert (x = fzero \/ exists x', x = fsucc x') as Hx. { apply Fin_cases. }
  destruct Hx as [Hx1 | Hx2].
  rewrite Hx1.
  assert (y = fzero \/ exists y', y = fsucc y') as Hy. { apply Fin_cases. }
  destruct Hy as [Hy1 | Hy2].
  rewrite Hy1.
  reflexivity.
  destruct Hy2 as [y' Hy2].
  rewrite Hy2.
  intro Abs.
  assert (label (@fzero p) <> label (fsucc y')) as T.
  rewrite Z_n_label_fzero.
  rewrite Z_n_label_fsucc.
  lia.
  contradiction.

  destruct Hx2 as [x' Hx2].
  rewrite Hx2.
  assert (y = fzero \/ exists y', y = fsucc y') as Hy. { apply Fin_cases. }
  destruct Hy as [Hy1 | Hy2].
  rewrite Hy1.
  intro Abs.
  assert (label (fsucc x') <> label (@fzero p)) as T.
  rewrite Z_n_label_fzero.
  rewrite Z_n_label_fsucc.
  lia.
  contradiction.
  destruct Hy2 as [y' Hy2].
  rewrite Hy2.
  repeat rewrite Z_n_label_fsucc.
  intro H.
  assert (label x' = label y') as H2.
  lia.
  assert (x' = y') as H3.
  apply IHp.
  assumption.
  rewrite H3.
  reflexivity.
Qed.


Notation "n % m" := (Nat.modulo n m) (at level 20) : type_scope.

Lemma Z_n_label_succ : forall {p:nat} (x:Z_n (S p)), label (succ x) = (S (label x)) % (S p).
Proof.
  apply Fin_ind_succ with (P:=fun p x => label (succ x) = (S (label x)) % (S p)).
  intro p.
  rewrite Z_n_label_fzero.
  destruct p.
  simpl.
  reflexivity.
  assert (label (succ (@fzero (S p))) = 1) as H. {
    simpl.
    reflexivity.
  }
  rewrite H.
  Check PeanoNat.Nat.mod_small.
  assert (forall n m:nat, n = m <-> m = n) as L. { lia. }
  rewrite L.
  apply PeanoNat.Nat.mod_small.
  lia.
  intros p x IH.
  destruct p.
  assert (x = fzero) as H2.
  apply Fin_1_all_fzero.
  rewrite H2.
  simpl.
  reflexivity.

  assert (succ x = fzero \/ exists y, succ x = fsucc y) as H.
  apply Fin_cases.
  destruct H as [H1 | H2].
  assert (succ (fsucc x) = fzero) as H2.
  simpl.
  rewrite H1.
  reflexivity.
  rewrite H2.
  rewrite Z_n_label_fsucc.
  rewrite @Z_n_label_last with (p:=S p).
  rewrite Z_n_label_fzero.
  assert (forall n m:nat, n = m <-> m = n) as L. { lia. }
  rewrite L.
  apply PeanoNat.Nat.mod_same.
  lia.
  assumption.

  destruct H2 as [y H2].
  assert (succ (fsucc x) = fsucc (fsucc y)) as H3.
  simpl.
  rewrite H2.
  reflexivity.
  rewrite H3.
  rewrite <- H2.
  repeat rewrite Z_n_label_fsucc.
  rewrite IH.
  assert (forall n m, n < S m -> (S ((S n) % (S (S m))) = (S (S n)) % (S (S (S m))))) as L. {
    intros n m C.
    assert ((S n) % (S (S m)) = S n) as S1.
    assert (S n < S (S m)) as C'.
    lia.
    apply PeanoNat.Nat.mod_small.
    assumption.
    assert ((S (S n)) % (S (S (S m))) = S (S n)) as S2.
    assert (S (S n) < S (S (S m))) as C'.
    lia.
    apply PeanoNat.Nat.mod_small.
    assumption.
    rewrite S1.
    rewrite S2.
    reflexivity.
  }
  rewrite L.
  reflexivity.
  apply @Z_n_label_before_last with (p:=S p).
  exists y.
  assumption.
Qed.

Lemma nat_succ_mod_idemp_r : forall a p:nat, (S (a % (S p))) % (S p) = (S a) % (S p).
Proof.
  intros a p.
  assert (forall n, S n = 1 + n) as L. { lia. }
  rewrite L.
  rewrite L with (n:=a).
  rewrite PeanoNat.Nat.add_mod_idemp_r.
  reflexivity.
  lia.
Qed.

Lemma Z_n_op_label {p:nat} : forall (x y:Z_n (S p)),
  label (Z_n_op x y) = (label x + label y) % (S p).
Proof.
  intros x y.
  unfold Z_n_op.
  set (k:=label y).
  induction k.
  assert (label (iter 0 succ x) = label x) as H.
  simpl.
  reflexivity.
  rewrite H.
  assert (label x + 0 = label x) as H2.
  lia.
  rewrite H2.
  assert (forall n m:nat, n = m <-> m = n) as L. { lia. }
  rewrite L.
  apply PeanoNat.Nat.mod_small.
  apply Z_n_label_bounded.
  rewrite iter_succ.
  rewrite Z_n_label_succ.
  rewrite IHk.
  set (l:=label x).
  assert (l + S k = S (l + k)) as L. { lia. }
  rewrite L.
  apply nat_succ_mod_idemp_r.
Qed.

Lemma Z_n_inv_label {p:nat} : forall (x:Z_n (S p)), label (Z_n_inv x) = ((S p) - label x) % (S p).
Proof.
  intro x.
  unfold Z_n_inv.
  set (k:=label x).
  assert ((S p) - k = S (p - k)) as H. {
    assert (k <= p) as H. {
      assert (S k <= S p) as H. { apply Z_n_label_bounded. }
      lia.
    }
    lia.
  }
  rewrite H.
  rewrite iter_succ.
  rewrite Z_n_label_succ.
  set (m:=p - k).
  assert (label (iter m succ (@fzero p)) = m % (S p)) as H2. {
    induction m.
    simpl.
    lia.
    rewrite iter_succ.
    assert (label (succ (iter m succ (@fzero p))) = (S (label (iter m succ (@fzero p))) % (S p))) as H2. {
      rewrite Z_n_label_succ.
      reflexivity.
    }
    rewrite H2.
    rewrite IHm.
    apply nat_succ_mod_idemp_r.
  }
  rewrite H2.
  apply nat_succ_mod_idemp_r.
Qed.

Theorem Z_n_group (p:nat) : Group.
Proof.
  apply (const_kozos (Z_n (S p)) (@Z_n_op p) (@Z_n_inv p) (@fzero p)).
  intros a b c.
  - assert (forall x y z n, n<>0 -> (x + ((y + z) % (n))) % (n) = (((x + y) % (n)) + z) % (n)) as L. {
      intros x y z n H.
      rewrite PeanoNat.Nat.add_mod_idemp_r.
      rewrite PeanoNat.Nat.add_mod_idemp_l.
      rewrite PeanoNat.Nat.add_assoc.
      reflexivity.
      assumption.
      assumption.
    }
    assert (label (Z_n_op a (Z_n_op b c)) = (label a + ((label b + label c) % (S p))) % (S p)) as S1.
    repeat rewrite Z_n_op_label.
    reflexivity.
    assert (label (Z_n_op (Z_n_op a b) c) = ((label a + label b) % (S p) + label c) % (S p)) as S2.
    repeat rewrite Z_n_op_label.
    reflexivity.
    rewrite L in S1.
    assert (label (Z_n_op a (Z_n_op b c)) = label (Z_n_op (Z_n_op a b) c)) as H.
    rewrite <- S2 in S1.
    rename S1 into H.
    clear S2.
    assumption.
    apply Z_n_label_inj.
    assumption.
    lia.
  - intro a.
    split.
    + assert (label (Z_n_op a fzero) = label a) as H.
      rewrite Z_n_op_label.
      rewrite Z_n_label_fzero.
      assert (label a + 0 = label a) as H. { lia. }
      rewrite H.
      apply PeanoNat.Nat.mod_small.
      apply Z_n_label_bounded.
      apply Z_n_label_inj.
      assumption.
    + assert (label (Z_n_op fzero a) = label a) as H.
      rewrite Z_n_op_label.
      rewrite Z_n_label_fzero.
      assert (0 + label a = label a) as H. { lia. }
      rewrite H.
      apply PeanoNat.Nat.mod_small.
      apply Z_n_label_bounded.
      apply Z_n_label_inj.
      assumption.
  - intro a.
    split.
    + assert (label (Z_n_op a (Z_n_inv a)) = label (@fzero p)) as H.
      rewrite Z_n_op_label.
      rewrite Z_n_label_fzero.
      rewrite Z_n_inv_label.
      assert (label a < S p) as H. { apply Z_n_label_bounded. }
      set (l:=label a).
      set (n:=S p).
      assert (n <> 0) as H2. { lia. }
      assert (l < n) as H'. { assumption. }
      assert (forall j m, m <> 0 -> j <= m -> (j + (m - j) % (m)) % (m) = 0) as L. {
        intros j m H3 H4.
        assert (j = 0 \/ j > 0) as H5. { lia. }
        destruct H5 as [H5_1 | H5_2].
        rewrite H5_1.
        assert (m - 0 = m) as L. { lia. }
        rewrite L.
        rewrite PeanoNat.Nat.mod_same.
        apply PeanoNat.Nat.mod_0_l.
        assumption.
        assumption.
        set (k:=m - j).
        assert (k < m) as H6. { lia. }
        rewrite PeanoNat.Nat.mod_small with (a:=k).
        subst k.
        assert (j + (m - j) = (m - j) + j) as H7. { lia. }
        rewrite H7.
        rewrite PeanoNat.Nat.sub_add.
        apply PeanoNat.Nat.mod_same.
        assumption.
        assumption.
        assumption.
      }
      apply L.
      assumption.
      lia.
      apply Z_n_label_inj.
      assumption.
    + assert (label (Z_n_op (Z_n_inv a) a) = label (@fzero p)) as H.
      rewrite Z_n_op_label.
      rewrite Z_n_label_fzero.
      rewrite Z_n_inv_label.
      assert (label a < S p) as H. { apply Z_n_label_bounded. }
      set (l:=label a).
      set (n:=S p).
      assert (n <> 0) as H2. { lia. }
      assert (l < n) as H'. { assumption. }
      assert (forall j m, m <> 0 -> j <= m -> ((m - j) % (m) + j) % (m) = 0) as L. {
        intros j m H3 H4.
        assert (j = 0 \/ j > 0) as H5. { lia. }
        destruct H5 as [H5_1 | H5_2].
        rewrite H5_1.
        assert (m - 0 = m) as L. { lia. }
        rewrite L.
        rewrite PeanoNat.Nat.mod_same.
        apply PeanoNat.Nat.mod_0_l.
        assumption.
        assumption.
        set (k:=m - j).
        assert (k < m) as H6. { lia. }
        rewrite PeanoNat.Nat.mod_small with (a:=k).
        subst k.
        rewrite PeanoNat.Nat.sub_add.
        apply PeanoNat.Nat.mod_same.
        assumption.
        assumption.
        assumption.
      }
      apply L.
      assumption.
      lia.
      apply Z_n_label_inj.
      assumption.
Qed.
