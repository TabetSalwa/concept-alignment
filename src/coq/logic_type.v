Require Import connectives_type.

Module Type Logic_Type (C : Connectives_Type).
Parameter eq : forall (A:Type), A -> A -> Prop.
Axiom refl : forall A, forall (x:A), eq (A) x x.
Axiom eq_ind : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq (A) x y) -> P y.
Axiom eq_rect_r : forall A, forall (a:A), forall (x:A), (eq (A) x a) -> forall (P:(A -> Prop)), (P a) -> P x.
Axiom eq_ind_r : forall A, forall (a:A), forall (P:(A -> Prop)), (P a) -> forall (x:A), (eq (A) x a) -> P x.
Axiom rewrite_l : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq (A) x y) -> P y.
Axiom sym_eq : forall A, forall (x:A), forall (y:A), (eq (A) x y) -> eq (A) y x.
Axiom rewrite_r : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq (A) y x) -> P y.
Axiom eq_coerc : forall (A:Prop), forall (B:Prop), A -> (eq (Prop) A B) -> B.
Axiom absurd : forall (A:Prop), A -> (C.Not A) -> C.False.
Axiom not_to_not : forall (A:Prop), forall (B:Prop), (A -> B) -> (C.Not B) -> C.Not A.
Axiom sym_not_eq : forall A, forall (x:A), forall (y:A), (C.Not (eq (A) x y)) -> C.Not (eq (A) y x).
End Logic_Type.
