Set Allow StrictProp.

Inductive Squash (A : Type) : SProp := squash :  A -> Squash A.
Arguments squash {_}.
Hint Constructors Squash : sprop.
Ltac squash := apply squash.

Inductive sFalse : SProp :=.

Inductive sTrue : SProp := sI.

Inductive sAnd (A : SProp) (B : SProp) : SProp := sConj : A -> B -> sAnd A B.
Arguments sConj {_} {_}. 
Infix "s/\" := sAnd (at level 20).
Hint Constructors sAnd : sprop.

Inductive sOr (A : SProp) (B: SProp) : SProp :=
  sInl : A -> sOr A B
| sInr : B -> sOr A B.
Infix "s\/" := sOr (at level 19).
Arguments sInl {_} {_}.
Arguments sInr {_} {_}.
Hint Constructors sOr : sprop.

Definition StrictTrue : sTrue -> True :=  fun _ => I.
Definition StrictTrueInv : True -> sTrue := fun _ => sI.
Coercion StrictTrue : sTrue >-> True.
Coercion StrictTrueInv : True >-> sTrue.

Definition StrictFalse : sFalse -> False := fun sf => match sf with end.
Definition StrictFalseInv : False -> sFalse := fun f => match f with end.
Coercion StrictFalse : sFalse >-> False.
Coercion StrictFalseInv : False >-> sFalse.
Ltac sexfalso := exfalso; apply StrictFalse.

Definition SquashAnd : forall {A B : Prop}, Squash (A /\ B) -> Squash A s/\ Squash B :=
  fun A B sq =>
    match sq with
      squash ab =>
      match ab with
        conj a b => sConj (squash a) (squash b)
      end
    end.

Definition AndSquash : forall {A B : Prop}, Squash A s/\ Squash B -> Squash (A /\ B) :=
  fun A B sab =>
    match sab with
      sConj sa sb =>
      match sa with
      | squash a =>
        match sb with
        | squash b => squash (conj a b)
        end
      end
    end.
Definition SquashOr : forall {A B : Prop}, Squash (A \/ B) -> Squash A s\/ Squash B :=
  fun A B sab =>
    match sab with
    | squash ab =>
      match ab with
      | or_introl a => sInl (squash a)
      | or_intror b => sInr (squash b)
      end
    end.
Definition OrSquash : forall {A B : Prop}, Squash A s\/ Squash B -> Squash (A \/ B) :=
  fun A B sab =>
    match sab with
    | sInl sa => match sa with squash a => squash (or_introl a) end
    | sInr sb => match sb with squash b => squash (or_intror b) end
    end.
Definition SquashFA : forall {A B : Prop}, Squash (forall x : A, B) -> forall x : Squash A, Squash B :=
  fun A B sf x =>
    match sf with
    | squash f => match x with squash y => squash (f y) end
    end.

