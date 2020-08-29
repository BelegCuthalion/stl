Require Import List.
Require Import lang.
Require Import iSTL.
Import List.ListNotations.
Coercion form_to_some (P : form) : (option form) := Some P.
Coercion list_to_form (P : form) : (list form) := [P].
Reserved Notation "G ⇒g D" (no associativity, at level 61). (* 21d2 *)

Inductive GSTL : list form -> option form -> Prop :=
  | Id:     forall a : form, a ⇒g a (* iSTL [p] p *)
  | Ta:     [] ⇒g ⊤
  | Ex:     forall n, n^∇ ⊥ ⇒g None
  | Lw:     forall G D p, G ⇒g D -> p::G ⇒g D
  | Rw:     forall G p, G ⇒g None -> G ⇒g p
  | Lc:     forall G D p, p::p::G ⇒g D -> p::G ⇒g D
  | La1:    forall G D (a b : form) n, (n^∇ a)::G ⇒g D -> (n^∇ (a ∧ b))::G ⇒g D
  | La2:    forall G D (a b : form) n, (n^∇ b)::G ⇒g D -> (n^∇ (a ∧ b))::G ⇒g D
  | Ra:     forall G (a b : form), G ⇒g a -> G ⇒g b -> G ⇒g (a ∧ b)
  | Lo:     forall G D (a b : form) n, (n^∇ a)::G ⇒g D -> (n^∇ b)::G ⇒g D -> (n^∇ (a ∨ b))::G ⇒g D
  | Ro1:    forall G (a b : form), G ⇒g a -> G ⇒g (a ∨ b)
  | Ro2:    forall G (a b : form), G ⇒g b -> G ⇒g (a ∨ b)
  | Li:     forall G D (a b : form) n, G ⇒g n^∇ a -> (n^∇ b)::G ⇒g D -> ((n+1)^∇ (a ⊃ b))::G ⇒g D
  | Ri:     forall G S (a b : form), ∇l S = G -> a::G ⇒g b -> S ⇒g (a ⊃ b)
  | N:      forall G a, G ⇒g Some a -> ∇l G ⇒g Some (∇ a)
  | Cut:    forall (a : form) G S D, G ⇒g a -> a::S ⇒g D -> G++S ⇒g D
  | Exc:    forall G S D a b, G++a::b::S ⇒g D -> G++b::a::S ⇒g D
where "G ⇒g D" := (GSTL G D).
