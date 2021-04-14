Require Import Omega List.
Require Import List.
Print list.
Print nil.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Open Scope list_scope.

Definition szam(k:option(nat)):nat:=
  match k with
  | None => 0
  | Some k => k
  end.



Fixpoint listaszum(k:list(option(nat))):nat:=
  match k with
  | nil => 0
  | cons x l' => szam x+ listaszum l'
  end.


Eval compute in listaszum (Some(2)::None::Some(4)::nil).

Require Import NAxioms NProperties OrdersFacts.

Print min_l.

Eval compute in Init.Nat.min 5 6.

Fixpoint listakicsi(k:list(option(nat))):nat:=
  match k with
  | nil => 0
  | cons x l' => Init.Nat.min (szam x) (listakicsi l')
  end.

Eval compute in listakicsi (Some(2)::None::Some(4)::nil).

Print Init.Nat.

Eval compute in (Init.Nat.eqb(Init.Nat.min 5 6)  (5)).


Definition MinPairTwo(x y : option (nat*nat)) : nat :=
  match x, y with
    | None, None => 0
    | None, Some (b,m) => b
    | Some (a,n), None => a
    | Some (a, n), Some (b, m) =>  match (Init.Nat.eqb(Init.Nat.min n m)(n)) with
          |true => a
          |_ => b
          end
  end.

Definition MinPairTwoVege(x y : option (nat*nat)) : option(nat*nat) :=
  match x, y with
    | None, None => None
    | None, Some (b,m) => Some(b,m)
    | Some (a,n), None => Some(a,n)
    | Some (a, n), Some (b, m) =>  match (Init.Nat.eqb(Init.Nat.min n m)(n)) with
          |true => Some(a,n)
          |_ => Some(b,m)
          end
  end.

Definition elsokinyer (x:option(nat*nat)):option(nat):=
  match x with
  |None => None
  |Some(a,b)=>Some(a)
  end.

Eval compute in MinPairTwoVege (Some(2,3)) (Some (1,4)).


Fixpoint listaminpar(k:list(option(nat*nat))):option(nat*nat):=
  match k with
  | nil => None
  | cons x l' => MinPairTwoVege(x) (listaminpar l')
  end.

Definition legkisebbpar (k:list(option(nat*nat))):option(nat):=
  elsokinyer (listaminpar k).

Eval compute in legkisebbpar (Some(2,3)::None::Some(4,1)::Some(88,0)::nil).

