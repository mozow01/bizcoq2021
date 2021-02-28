Load bizcoq_2_hf_2.

(* hf *)

(*
Definition EpiMorphismCat (X:Type) (Y:Type) (f:X->Y) : Prop :=
  forall Z:Type g h:Y->Z,
    (forall x:X, g (f x) = h (f x)) -> (forall y:Y, g y = h y).
*)

Definition EpiMorphism (G:Group) (H:Group) (f:G->H) : Prop :=  
  forall h:H, exists g:G, f g = h.

Theorem f_Z_6_Z_3_em : EpiMorphism (Z_6_group) (Z_3_group) f_Z_6_Z_3.
Proof.
  unfold EpiMorphism.
  induction h.
  unfold f_Z_6_Z_3.
  exists z_6_0; auto.
  exists z_6_1; auto.
  exists z_6_2; auto.
Qed.

Theorem f_Z_6_Z_1_em : EpiMorphism (Z_6_group) (Z_1_group) f_Z_6_Z_1.
Proof.
  unfold EpiMorphism.
  induction h.
  unfold f_Z_6_Z_1.
  exists z_6_0; auto.
Qed.
