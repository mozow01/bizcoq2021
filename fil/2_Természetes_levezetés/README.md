# A nyelvi jelentés használatelmélete és az induktív adattípusok

## A szavak jelentését a használatuk határozza meg
# Induktív érvelés, harmónia

Az induktív adattípusoknál sem azt mondjuk meg, hogy mik ezek, hanem hogy használni hogyan kell őket. Ez egy nyelvhasználati program következetes kivitelezése és nem pusztán analógia. Michael Dummettre és Dag Prawitzra közvetlenül hivatkoznak ebben a tudományban a programozók.

Dummett Wittgenstein egy ötletét vitte tovább a logikafilozófiában, Prawitz pedig Gerhard Gentzen egy sejtését dolgozta ki és építette be az analitikus nyelvfilozófia érvelési gyakorlatába.

"A bevezetési szabály, hogy úgy mondjuk definiálja a kérdéses szót, (...) a kiküszöbölési szabály csak egy következménye a megfelelő bevezetési szabálynak, és ez így foglalható össze: egy kiküszübölési szabály alkalmazásakor csak azt használhatjuk amilyen jelentést a bevezetési szabály adott a szónak." (Gentzen)

Ez a _harmónia_ feltevése. És valóban! A kiküszöbölési szabályokat a Coq automatikusan generálni tudja az induktív definíciót követően. 


## Rekurzív nyelvek és algoritmusokkal kapcsolatos hatékonyság

````coq
(*Utasítás*)

Inductive Instruction : Set :=
  | And : Instruction
  | Or : Instruction.

(*Program*)

Inductive ParallelProgram : Set :=
  | leaf : nat -> ParallelProgram
  | node : Instruction -> ParallelProgram -> ParallelProgram -> ParallelProgram.

(*Program output*)

Fixpoint ProgOut (p: ParallelProgram) (v : nat -> bool) :=
match p with
  | leaf n => v n
  | node x p1 p2 => match x with
           | And => andb (ProgOut p1 v) (ProgOut p2 v)
           | Or => orb (ProgOut p1 v) (ProgOut p2 v)
                     end
end.

(*Nyelv*)

Inductive Expression : Set :=
  | VAR : nat -> Expression   
  | AND : Expression -> Expression  -> Expression  
  | OR : Expression -> Expression  -> Expression.

(*Denotáció*)

Fixpoint ExpDenote (e : Expression) (v : nat -> bool ) :=
match e with 
  | VAR n => v n 
  | AND e1 e2 => andb (ExpDenote e1 v) (ExpDenote e2 v)
  | OR e1 e2 => orb (ExpDenote e1 v) (ExpDenote e2 v)
end.

(*Fordítások*)

Fixpoint Translate_1 (e : Expression) :=
match e with
  | VAR n => leaf n 
  | AND e1 e2 => node And (Translate_1 e1) (Translate_1  e2)
  | OR e1 e2 => node Or (Translate_1  e1) (Translate_1  e2)
end.

Fixpoint Translate_2 (p : ParallelProgram) :=
match p with
  | leaf n => VAR n
  | node And p1 p2 => AND (Translate_2 p1) (Translate_2 p2)
  | node Or p1 p2 => OR (Translate_2 p1) (Translate_2 p2) 
end.

(*Programhelyesség*)

Theorem Soundness_1 : forall p v, ProgOut p v = ExpDenote (Translate_2 p) v.
Proof.
intros.
induction p.
compute.
auto.
induction i.
all: simpl; rewrite IHp1; rewrite IHp2; auto.
Show Proof.
Qed.

Theorem Soundness_2 : forall e v, ExpDenote e v = ProgOut (Translate_1 e) v.
Proof.
intros.
induction e.
compute.
auto.
all: simpl; rewrite IHe1; rewrite IHe2; auto.
Show Proof.
Qed.
````








