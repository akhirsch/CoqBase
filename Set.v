Require Export Coq.Bool.Bool.
Section BoolSet.



  Open Scope bool_scope.
  
  Variable A : Set.

  Definition bset : Set := A -> bool.

  (* In as a proposition *)
  Definition bset_in : A -> bset -> Prop :=
    fun a s => s a = true.
  Lemma bset_in_dec : forall (a : A) (s : bset), {bset_in a s} + {~bset_in a s}.
  Proof.
    intros a s.
    unfold bset_in. destruct (s a). left; auto. right; intro H; inversion H.
  Qed.


  (* Unions *)
  Definition bset_union : bset -> bset -> bset :=
    fun s1 s2 a => s1 a || s2 a.
  Lemma bset_union_in_l : forall (a : A) (s1 s2 : bset), bset_in a s1 -> bset_in a (bset_union s1 s2).
  Proof.
    intros a s1 s2 H.
    unfold bset_union. unfold bset_in. unfold bset_in in H. rewrite H. auto.
  Qed.
  Lemma bset_union_in_r : forall (a : A) (s1 s2 : bset), bset_in a s2 -> bset_in a (bset_union s1 s2).
  Proof.
    intros a s1 s2 H.
    unfold bset_union. unfold bset_in in *.  rewrite H. destruct (s1 a); auto.
  Qed.
  Lemma bset_union_lub : forall (a : A) (s1 s2 s3 : bset), (bset_in a s1 -> bset_in a s3) -> (bset_in a s2 -> bset_in a s3) -> bset_in a (bset_union s1 s2) -> bset_in a s3.
  Proof.
    intros a s1 s2 s3 H H0 H1.
    unfold bset_in in *; unfold bset_union in H1.
    destruct (orb_prop _ _ H1); auto.
  Qed.

  