Require Export IndProp.
Import Omega.

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)



Inductive subseq {X : Type} : list X -> list X -> Prop :=
  | sub_nil : subseq nil nil
  | sub_addr : forall n l1 l2, subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_addl : forall n l1 l2, subseq l1 l2 -> subseq (n :: l1) (n :: l2).

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P nil
  | all_app : forall n l, all X P l -> P n -> all X P (n :: l).

Theorem subseq_length : forall (X : Type) (m l : list X), subseq m l -> length m <= length l.
 Proof.
  intros X m l h.
  induction h.
  - simpl. apply le_n.
  - simpl. omega.
  - simpl. omega.
Qed.

Theorem le_false : forall n : nat, S n <= n -> False.
Proof.
  intros n H.
  induction n.
  - inversion H.
  - apply IHn. omega.
Qed.

Lemma subseq_length_equal : forall (X : Type) (l1 l2 : list X),
  subseq l1 l2 -> length l2 <= length l1 -> l1 = l2.
Proof.
  intros X l1 l2 H1 H2.
  induction H1.
  - reflexivity.
  - apply subseq_length in H1.
    simpl in H2.
    assert (H3 : S (length l2) <= length l2).
    {
      apply le_trans with (length l1).
      apply H2.
      apply H1.
    }
    apply le_false in H3.
    inversion H3.
  - apply f_equal.
    apply IHsubseq.
    simpl in H2.
    apply Sn_le_Sm__n_le_m.
    apply H2.
Qed.

Lemma filter_subseq : forall (X : Type) (f : X -> bool) (l l' : list X),
  all X (fun x => f x = true) l' -> subseq l' l -> subseq l' (filter f l).
Proof.
  intros X f l l' H1 H2.
  induction H2.
  - Search nil. apply sub_nil.
  - simpl. destruct (f n).
    + apply sub_addr. apply IHsubseq. apply H1.
    + apply IHsubseq. apply H1.
  - simpl. inversion H1. rewrite H4. apply sub_addl. apply IHsubseq. apply H3.
Qed.

Lemma filter_all : forall (X : Type) (f : X -> bool) (l : list X),
  all X (fun x => f x = true) (filter f l) /\ subseq (filter f l) l.
Proof. 
  split.
  - induction l.
    + apply all_nil.
    + simpl. destruct (f x) eqn:eqn1.
      * apply all_app. apply IHl. apply eqn1.
      * apply IHl.
  - induction l.
    + apply sub_nil.
    + simpl. destruct (f x).
      * apply sub_addl. apply IHl.
      * apply sub_addr. apply IHl.
Qed.

Theorem filter_challenge_2 : forall (X : Type) (f : X -> bool) (l1 l2 : list X),
  all X (fun x => f x = true) l2 -> subseq l2 l1 -> (forall l3 : list X, 
  all X (fun x => f x = true) l3 -> subseq l3 l1 -> length l3 <= length l2) ->
  filter f l1 = l2.
Proof.
  intros X f l1 l2 H1 H2 H3.
  symmetry.
  apply subseq_length_equal.
  apply filter_subseq. apply H1. apply H2. apply H3.
  apply filter_all. apply filter_all.
Qed.
