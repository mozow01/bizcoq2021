Definition csak3(k:nat):bool:=
  match k with
  |3 => true
  |_ => false
  end.


Definition haromnalkisebb(k:nat):bool:=
negb(Init.Nat.eqb(Init.Nat.min k 3)(3)).

Eval compute in haromnalkisebb 1.

Definition mkisebb (m:nat)(n:nat):bool:=
  match Init.Nat.eqb m n with
  | true => false
  | false => (Init.Nat.eqb(Init.Nat.min m n)(m))
  end.


Eval compute in mkisebb 2 3.
 