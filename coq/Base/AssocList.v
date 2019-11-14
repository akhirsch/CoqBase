Require Export List.
Require Export Option.
Require Import Base.SProp.

Set Allow StrictProp.


Import ListNotations.
Section Lookup.

  Variable A B : Type.
  Variable A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

  Fixpoint al_lookup (l : list (A * B)) (k : A) : option B :=
    match l with
    | [] => None
    | (x :: l) => match x with
                | (a, b) => if A_eq_dec k a then Some b else al_lookup l k
                end
    end.

  Program Fixpoint al_lookup_in (l : list (A * B)) (k : A) : Squash (exists v, In (k,v) l) -> B :=
    fun i =>
      match l with
      | [] => _
      | (x :: l) => match x with
                  | (a,b) => if A_eq_dec k a then b else al_lookup_in l k _
                  end
      end.
  Next Obligation.
    sexfalso. destruct i as [i]; destruct i as [v i]. inversion i.
  Defined.
  Next Obligation.
    destruct i as [i]; destruct i as [v i]; inversion i.
    - destruct H; inversion H0; reflexivity.
    - squash. exists v. exact H0.
  Defined.

  Theorem al_lookup_In : forall (l : list (A * B)) (k : A) (i : exists v, In (k,v) l),
      al_lookup l k = Some (al_lookup_in l k (squash i)).
  Proof.
    intros l k i.
    induction l as [| p l]; simpl.
    inversion i; inversion H.
    destruct p as [a b]. destruct (A_eq_dec k a). reflexivity.
    assert (exists v : B, In (k, v) l). destruct i as [v i]; exists v; inversion i.
    destruct n; inversion H; reflexivity. exact H.
    apply (IHl H).
  Qed.
  Theorem al_lookup_notIn : forall (l : list (A * B)) (k : A),
      al_lookup l k = None -> forall v : B, ~ In (k, v) l.
  Proof.
    intros l k H.
    induction l; auto; intro v.
    simpl in H. destruct a. destruct (A_eq_dec k a).
    inversion H. intro i; inversion i.
    apply n; inversion H0; reflexivity.
    apply (IHl H v H0).
  Qed.
End Lookup.
Arguments al_lookup {_} {_}.
Arguments al_lookup_in {_} {_}.
Arguments al_lookup_In {_} {_}.

Section ProperAssocList.
  Variable A B : Type.
  
  Definition proper_al : list (A * B) -> Prop :=
    fun l => forall k v v', In (k,v) l -> In (k,v') l -> v = v'.
End ProperAssocList.
Arguments proper_al {_} {_}.

Section Remove.
  Variable A B : Type.
  Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.

  Fixpoint al_remove (l : list (A * B)) (k : A) : list (A * B) :=
    match l with
    | [] => []
    | x :: l => match x
              with (a, b) =>
                   if A_eq_dec k a
                   then al_remove l k
                   else (a, b) :: al_remove l k
              end
    end.

  Theorem al_remove_In : forall (l : list (A * B)) (k : A) (v : B), ~ In (k, v) (al_remove l k).
  Proof.
    intro l; induction l; intros k v; intro H; simpl in H.
    inversion H.
    destruct a. destruct (A_eq_dec k a).
    apply (IHl k v H).
    inversion H; [destruct n; inversion H0; reflexivity|].
    apply (IHl k v H0).
  Qed.    
End Remove.
Arguments al_remove {_} {_}.
Arguments al_remove_In {_} {_}.
Unset Implicit Arguments.
