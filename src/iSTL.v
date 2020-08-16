Require Import List.
Require Import lang.
Import List.ListNotations.
Coercion form_to_some (P : form) : (option form) := Some P.
Coercion list_to_form (P : form) : (list form) := [P].
Reserved Notation "G ⇒ D" (no associativity, at level 61). (* 21d2 *)

Inductive iSTL : list form -> option form -> Prop :=
  | Id:     forall a : form, a ⇒ a (* iSTL [p] p *)
  | Ta:     [] ⇒ ⊤
  | Ex:     ⊥ ⇒ None
  | Lw:     forall G D p, G ⇒ D -> p::G ⇒ D
  | Rw:     forall G p, G ⇒ None -> G ⇒ p
  | La1:    forall G D (a b : form), a::G ⇒ D -> (a ∧ b)::G ⇒ D
  | La2:    forall G D (a b : form), b::G ⇒ D -> (a ∧ b)::G ⇒ D
  | Ra:     forall G (a b : form), G ⇒ a -> G ⇒ b -> G ⇒ (a ∧ b)
  | Lo:     forall G D (a b : form), a::G ⇒ D -> b::G ⇒ D -> (a ∨ b)::G ⇒ D
  | Ro1:    forall G (a b : form), G ⇒ a -> G ⇒ (a ∨ b)
  | Ro2:    forall G (a b : form), G ⇒ b -> G ⇒ (a ∨ b)
  | Li:     forall G D (a b : form), G ⇒ a -> b::G ⇒ D -> ∇(a ⊃ b)::G ⇒ D
  | Ri:     forall G S (a b : form), ∇l S = G -> a::G ⇒ b -> S ⇒ (a ⊃ b)
  | N:      forall G a, G ⇒ Some a -> ∇l G ⇒ Some (∇ a)
  | Cut:    forall (a : form) G S D, G ⇒ a -> a::S ⇒ D -> G++S ⇒ D
  | Exc:    forall G S D a b, G++a::b::S ⇒ D -> G++b::a::S ⇒ D
where "G ⇒ D" := (iSTL G D).

Notation "⇒ p" := ([] ⇒ p) (no associativity, at level 62).

Lemma nabla_N : forall G (a : form) n, G ⇒ a -> n^∇l G ⇒ n^∇ a.
Proof.
  induction n.
    - simpl. rewrite map_id. intros H. apply H.
    - intros H. rewrite nabla_Nabl_list. simpl.
      apply IHn in H. apply N in H. apply H.
Qed.

Lemma nabla_form : forall a b : form, [a] ⇒ Some b -> [∇ a] ⇒ Some (∇ b).
Proof. intros. rewrite nabla_singleton. rewrite nabla_some. apply N. apply H. Qed.

Lemma nabla_n_form : forall n (a b : form), [a] ⇒ Some b -> [n^∇ a] ⇒ Some (n^∇ b).
Proof. intros. rewrite nabla_n_singleton. rewrite nabla_n_some. apply nabla_N. apply H. Qed.

Lemma nabla_n_dist_and : forall a b n, [n^∇ (a ∧ b)] ⇒ n^∇ a ∧ n^∇ b.
Proof.
  intros.
  apply Ra;
    rewrite nabla_n_some; rewrite nabla_n_singleton; apply nabla_N.
    - apply La1. apply Id.
    - apply La2. apply Id.
Qed.

Lemma nabla_box : forall a, ∇ (⎕ a) ⇒ a.
Proof. intros. apply Li. apply Ta. apply Id. Qed.

Lemma box_nabla: forall a : form, a ⇒ ⎕ ∇ a.
Proof.
  intros. apply (Ri [∇a]). reflexivity.
  apply Lw. apply Id.
Qed.

Lemma nabla_dist_or : forall a b, ∇ (a ∨ b) ⇒ ∇ a ∨ ∇ b.
Proof.
  intros. apply (Cut (∇(⎕ (∇ a ∨ ∇ b))) ([∇ (a ∨ b)]) nil (∇ a ∨ ∇ b)).
    - rewrite nabla_singleton. apply N.
      apply Lo.
        + apply (Ri [∇a]). reflexivity. apply Lw. apply Ro1. apply Id.
        + apply (Ri [∇b]). reflexivity. apply Lw. apply Ro2. apply Id.
    - apply nabla_box.
Qed.

Lemma nabla_n_dist_or : forall a b n, n^∇ (a ∨ b) ⇒ n^∇ a ∨ n^∇ b.
Proof.
  induction n. apply Id.
  apply (Cut (∇ (n^∇ a ∨ n^∇ b)) ([S n ^∇ (a ∨ b)]) []).
    - simpl. rewrite nabla_singleton. apply N. apply IHn.
    - apply nabla_dist_or.
Qed.

Lemma nabla_bot : ∇ ⊥ ⇒ ⊥.
Proof.
  apply (Cut (∇⎕⊥) (∇⊥)).
    - apply nabla_form. apply Rw. apply Ex.
    - apply nabla_box.
Qed.

Lemma nabla_n_bot : forall n m, n^∇ ⊥ ⇒ (n - m)^∇ ⊥.
Proof.
  induction m; simpl.
    - rewrite <- Minus.minus_n_O. apply Id.
    - apply (Cut ((n - m) ^∇ ⊥) (n ^∇ ⊥ )).
      + apply IHm.
      + rewrite PeanoNat.Nat.sub_succ_r.
        destruct (n - m).
          * simpl. apply Id.
          * unfold pred. rewrite nabla_Sn.
            apply nabla_n_form. apply nabla_bot.
Qed.

Tactic Notation "swap_hd" := apply (Exc [] _ _ _ _); simpl.

Lemma nabla_n_dist_impl : forall a b n, n^∇ (a ⊃ b) ⇒ n^∇ a ⊃ n^∇ b.
Proof.
  intros. apply (Ri [(S n)^∇ (a ⊃ b)]). reflexivity.
  rewrite nabla_Sn.
  assert (this : [n^∇ a; n^∇ ∇(a ⊃ b)] = n^∇l [a; ∇(a ⊃ b)]).
    { reflexivity. }
  rewrite this. apply nabla_N. swap_hd.
  apply Li.
    - apply Id.
    - swap_hd. apply Lw. apply Id.
Qed.

Lemma modus_ponens : forall a b : form, [∇(a ⊃ b); a] ⇒ b.
Proof. intros. apply Li.
    - apply Id.
    - swap_hd. apply Lw. apply Id.
Qed.

Lemma impl_elim : forall a b, ⇒ a ⊃ b -> a ⇒ b.
Proof.
  intros. apply (Cut (∇(a ⊃ b)) []).
    - unfold form_to_some. rewrite nabla_nil. apply N. apply H.
    - apply modus_ponens.
Qed.

Lemma list_app_cons : forall {A : Type} (l : list A) (a : A),
  a :: l = [a] ++ l.
Proof. reflexivity. Qed.

Lemma exc_a_lot : forall G S P D a,
  G ++ a::S ++ P ⇒ D -> G ++ S ++ a::P ⇒ D.
Proof.
  intros G S. generalize dependent G.
  induction S; intros; simpl in *.
    - apply H.
    - apply (Exc _ _ _ a0 a) in H.
      rewrite list_app_cons in H. rewrite app_assoc in H.
      apply (IHS (G ++ [a]) _ _ a0) in H.
      rewrite <- app_assoc in H. rewrite <- list_app_cons in H.
      apply H.
Qed.

Lemma weaken_a_lot : forall G S D, G ⇒ D -> G++S ⇒ D.
Proof.
  intros. induction S.
    - rewrite app_nil_r. apply H.
    - apply (Lw _ _ a) in IHS.
      apply (exc_a_lot [] G S D a) in IHS. apply IHS.
Qed.

Lemma conj_context : forall G : list form, G ⇒ list_conj G.
Proof.
  induction G.
    - apply Ta.
    - simpl. apply Ra.
      + rewrite list_app_cons. apply weaken_a_lot. apply Id.
      + apply Lw. apply IHG.
Qed.