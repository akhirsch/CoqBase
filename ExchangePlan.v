Require Import Base.Permutation.
Import ListNotations. Open Scope list_scope.

Definition ExchangePlan := list nat.

Section Exchange.
  Variable A : Type.

  Inductive OffByExchange : list A -> list A -> Prop :=
    OffByExchangeRefl : forall l, OffByExchange l l
  | Middles : forall l1 l2 a b, OffByExchange (l1 ++ a :: b :: l2) (l1 ++ b :: a :: l2).

  Lemma OffByExchangeNilNilL : forall (l : list A),
      OffByExchange [] l -> l = [].
  Proof.
    intros l H; inversion H; auto;
    assert (In a []) as Hnil by (rewrite <- H1; apply in_or_app; right; simpl; left; auto);
    exfalso; apply (in_nil Hnil).
  Qed.

  Lemma OffByExchangeNilNilR : forall (l : list A),
      OffByExchange l [] -> l = [].
  Proof.
    intros l H; inversion H; auto;
    assert (In a []) as Hnil
        by (rewrite <- H2; apply in_or_app; right; simpl; right; left; auto);
    exfalso; apply (in_nil Hnil).
  Qed.
  
  Lemma OffByExchangeSym : forall l l' : list A,
      OffByExchange l l' -> OffByExchange l' l.
  Proof.
    intros l l' H; induction H; constructor.
  Qed.
  Lemma OffByExchangeCons : forall (l l' : list A),
      OffByExchange l l' -> forall (x : A), OffByExchange (x :: l) (x :: l').
  Proof.
    intros l l' H; induction H; try constructor.
    intro x. apply Middles with (l1 := x :: l1) (l2 := l2).
  Qed.    

  Fixpoint Exchange (l : list A) (n : nat) {struct n} : list A :=
    match l with
    | [] => []
    | [x] => [x]
    | x :: y :: xs =>
      match n with
      | 0 => y :: x :: xs
      | S n' => x :: Exchange (y :: xs) n'
      end
    end.

  Lemma ExchangeNil : forall (n : nat), Exchange [] n = [].
  Proof.
    intros n; induction n; simpl; auto.
  Qed.
  
  Lemma ExchangeSingleton : forall (x : A) (n : nat), Exchange [x] n = [x].
  Proof.
    intros x n; induction n; simpl; auto.
  Qed.
  
  Theorem OffByExchangeCorrect : forall (l : list A) (n : nat),
      OffByExchange l (Exchange l n).
  Proof.
    intros l; induction l as [| x l]; simpl. intro n; rewrite ExchangeNil; constructor.
    destruct l as [| y l]; simpl; intro n.
    rewrite ExchangeSingleton; constructor.
    destruct n; simpl.
    apply Middles with (l1 := []).
    apply OffByExchangeCons; auto.
  Qed.    

  Theorem OffByExchangeAtNumber : forall l1 l2, OffByExchange l1 l2 -> exists n, Exchange l1 n = l2.
  Proof.
    intros l1 l2 Hex; destruct Hex.
    exists (length l); induction l; simpl; auto; destruct l; auto; rewrite IHl; auto.
    exists (length l1). induction l1; auto; simpl. destruct (l1 ++ a :: b :: l2) eqn:e.
    - assert (In a []) as Hnil by (rewrite <- e; apply in_or_app; right; simpl; left; auto);
        exfalso; apply (in_nil Hnil).
    - rewrite IHl1. auto.
  Qed.

  Theorem ExchangeGeneratesOffByExchange : forall l n, OffByExchange l (Exchange l n).
  Proof.
    intros l n; generalize dependent l; induction n; intro l; simpl.
    destruct l; [constructor | destruct l; [constructor | apply Middles with (l1 := [])]].
    destruct l. constructor. destruct l. constructor. apply OffByExchangeCons. apply IHn.
  Qed.

  Definition RunExchangePlan (l : list A) (e : ExchangePlan) :=
    fold_left Exchange e l.

  Inductive OffByExchanges : list A -> list A -> Prop :=
    OneExchange: forall l1 l2 : list A, OffByExchange l1 l2 -> OffByExchanges l1 l2
  | OffByExchangesTrans : forall l1 l2 l3 : list A,
      OffByExchanges l1 l2 -> OffByExchanges l2 l3 -> OffByExchanges l1 l3.

  Lemma OffByExchangesRefl : forall l : list A, OffByExchanges l l.
  Proof.
    intro l; apply OneExchange; constructor.
  Qed.
  
  Lemma OffByExchangesCons : forall (l1 l2 : list A), 
      OffByExchanges l1 l2 -> forall a, OffByExchanges (a :: l1) (a :: l2).
  Proof.
    intros l1 l2 Hobe; induction Hobe.
    intro a; apply OneExchange; apply OffByExchangeCons; auto.
    intro a; apply OffByExchangesTrans with (l2 := a :: l2);
      [apply IHHobe1 | apply IHHobe2]; auto.
  Qed.
  Theorem OffByExchangesIsPermutation : forall (l1 l2 : list A),
      Permutation l1 l2 <-> OffByExchanges l1 l2.
  Proof.
    intros l1 l2; split; intro H; induction H; try (repeat constructor; fail).
    apply OffByExchangesCons; auto.
    apply OneExchange; apply Middles with (l1 := []).
    apply OffByExchangesTrans with (l2 := l'); auto.
    destruct H; [auto | apply Permutation_app_head with (l := l1); constructor].
    apply Permutation_trans with (l' := l2); auto.
  Qed.

  Theorem RunExchangePlanCorr : forall (l : list A) (e : ExchangePlan),
      OffByExchanges l (RunExchangePlan l e).
  Proof.
    intros l e; generalize dependent l.
    induction e; intro l; simpl; auto. apply OffByExchangesRefl.
    apply OffByExchangesTrans with (l2 := Exchange l a); auto.
    apply OneExchange; apply ExchangeGeneratesOffByExchange.
  Qed.

  Theorem OffByExchangesCreatesExchangePlan : forall (l1 l2 : list A),
      OffByExchanges l1 l2 -> exists e : ExchangePlan, RunExchangePlan l1 e = l2.
  Proof.
    intros l1 l2 H; induction H.
    destruct (OffByExchangeAtNumber l1 l2 H) as [n Hn]; exists [n]; simpl; auto.
    destruct IHOffByExchanges1 as [e1 He1];
      destruct IHOffByExchanges2 as [e2 He2];
      exists (e1 ++ e2); unfold RunExchangePlan; rewrite fold_left_app;
        unfold RunExchangePlan in He1; rewrite He1;
          unfold RunExchangePlan in He2; rewrite He2; reflexivity.
  Qed.

End Exchange.