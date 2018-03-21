Require Import List Arith.

(* General instructions: Follow the specifc instructions below, and replace
every occurrence of "admitted" with your own code or proof. *)

(* Exercise 1 *)
(* Define an inductive predicate to specify lists whose length is even. *)
Inductive len_ev {A : Type}: list A -> Prop :=
  | ev_nil : len_ev nil
  | ev_ss  : forall {m n : A} {L : list A}, len_ev L -> len_ev (m::(n::L)).

(* Name this predicate "len_ev" *)

(* Use "Arguments len_ev {A} _." to make the type argument implicit *)

Lemma len_ev_example :
   forall a : nat, len_ev (a::(2*a)::(3*a)::(4*a)::nil).
Proof.
  intros. apply ev_ss. apply ev_ss. apply ev_nil.
  Qed.

(* Exercise 2 *)
(* Define an inductive predicate named "swapped" to express that list1 
   is the same as list2 where two consecutive elements have been
   swapped.
   - the first constructor specifies that the first two elements of the
     list have been swapped and the rest is the same for the two lists.
     For instance (swapped (1::3::2::4::nil) (3::1::2::4::nil)) should be
     provable using this constructor.
   - the second constructor specifies that the two lists have the same first
     element, but their tails have a swap in them.
     For instance (swapped (1::3::2::4::nil) (1::2::3::4::nil)) should have
     a proof that starts by using this constructor.
     This predicate should have three arguments: a type A and two lists of
     type A.  Make the type A an implicit argument using the command
     "Arguments swapped {A} _ _." *)
Inductive swapped {A : Type} : list A -> list A -> Prop :=
  | swapped_base : forall {h1 h2 : list A} {t1 t2 : A}, (h1 = h2) -> swapped (t1::(t2::h1)) (t2::(t1::h2))
  | swapped_tail : forall {h1 : A} {h3 h4 : list A}, swapped h3 h4 -> swapped (h1::h3) (h1::h4).

Lemma swapped_ex : swapped (1::3::2::4::nil) (1::2::3::4::nil).
Proof.
  apply swapped_tail.
  apply swapped_base.
  reflexivity.
Qed.
  

(* Exercise 3 *)
(* Define an inductive relation named "rearranged" that is satisfied by list1 list2 if
   one of the following cases is satisfied:
   1/ list1 and list2 are the same
   2/ list1 is a swap of list3 and list3 is a rearranged list2.
   Again, this relation should be polymorphic, and you should add an
   implicit argument declaration. *)
Inductive rearranged {A : Type} : list A -> list A -> Prop :=
  | c1 : forall list1 list2 : list A, (list1 = list2) -> rearranged list1 list2
  | c2 : forall list1 list2 list3: list A, (swapped list1 list3) /\ (rearranged list2 list3) -> rearranged list1 list2.

(* Exercise 4 *)
Lemma rearranged_refl : forall (A : Type) (list1 : list A), rearranged list1 list1.
Proof.
  intros. apply c1. reflexivity.
Qed.

Lemma rearranged_transitive : forall (A : Type) (list1 list2 list3 : list A),
  rearranged list1 list2 -> rearranged list2 list3 -> rearranged list1 list3.
Proof.
  intros.
  destruct H.
  - destruct H0.
    + rewrite H. rewrite <- H0. apply c1. reflexivity.
      Admitted.

Lemma swapped_sym : forall A (list1 list2:list A), swapped list1 list2 -> swapped list2 list1.
Proof.
  intros.
  induction H.
  - rewrite H. apply swapped_base. reflexivity.
  - apply swapped_tail. apply IHswapped.
Qed.

Lemma swapped_rearranged : forall (A : Type) (l1 l2 : list A), swapped l1 l2 -> rearranged l1 l2.
Proof.
  intros.
  apply c2 with (list3:=l2). split. apply H. apply c1. reflexivity.
Qed.

Lemma rearranged_sym : forall (A : Type) (list1 list2 : list A), rearranged list1 list2 -> rearranged list2 list1.
Proof.
  intros.
  induction H.
  - rewrite H. apply c1. reflexivity.
  - inversion H. apply swapped_sym in H0. apply swapped_rearranged in H0. apply rearranged_transitive with (list2:=list3). apply H1. apply H0.
Qed. 

Lemma rearranged_Tail : forall A (a:A) list1 list2, rearranged list1 list2 -> rearranged (a::list1) (a::list2).
Proof.
  intros. 
  inversion H.
  - rewrite H0. apply c1. reflexivity.
  - destruct H0. destruct list1.
    + inversion H0.
    + Admitted.
  

Fixpoint insert x l :=
  match l with 
    nil => x::nil
  | y::tl => if leb x y then x::l else y::insert x tl
  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | x::tl => insert x (sort tl)
  end.

(* Now prove that sorting a list returns an output that satisfies the rearranged relation on the input. *)

Lemma insert_rearranged : forall x l, rearranged (insert x l) (x::l).
Proof.
  intros.
  induction l.
  - unfold insert. apply c1. reflexivity.
  - simpl. destruct (x <=? a) eqn:eqn1.
    + apply c1. reflexivity.
    + apply rearranged_Tail with (a:=a) in IHl. apply rearranged_sym. apply c2 with (list3 := (a::x::l)). split. apply swapped_base. reflexivity. apply IHl.
Qed.

Lemma sort_rearranged : forall l, rearranged (sort l) l.
Proof.
  intros.
  induction l.
  - unfold sort. apply c1. reflexivity.
  - apply rearranged_Tail with (a:=a) in IHl. simpl. apply rearranged_sym in IHl. apply rearranged_transitive with (list2 := (a :: sort l)). apply insert_rearranged. apply rearranged_sym. apply IHl.
Qed.
