Require Import connectives_type.
Require Import logic_type.
Require Import connectives_coq.

Module Logic_make (C : Connectives_Type).
Definition eq {A} := @C.equal A.
Definition refl {A} : forall (x:A), @eq (A) x x := C.equal_refl A.
Definition eq_ind {A} : forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq x y) -> P y := fun (x:A) => fun (P : A -> Prop) => fun (Px : P x) => fun (y:A) => fun (e : eq x y) => @C.equal_leibniz A x y e P Px.
Definition eq_rect_r : forall A, forall (a:A), forall (x:A), (eq x a) -> forall (P:(A -> Prop)), (P a) -> P x := fun (A:Type) => fun (a:A) => fun (x:A) => fun (p:eq x a) => (((((eq_ind x) (fun (__:A) => forall (P:(A -> Prop)), (P __) -> P x)) (fun (P:A -> Prop) => fun (auto:P x) => (auto))) (a)) (p)).
Definition eq_ind_r : forall A, forall (a:A), forall (P:(A -> Prop)), (P a) -> forall (x:A), (eq x a) -> P x := fun (A:Type) => fun (a:A) => fun (P:A -> Prop) => fun (p:P a) => (fun (x0:A) => fun (p0:eq x0 a) => (((((((eq_rect_r) (A)) (a)) (x0)) (p0)) (fun (x01:A) => P x01)) (p))).
Definition rewrite_l : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq x y) -> P y := fun (A:Type) => fun (x:A) => fun (P:A -> Prop) => fun (Hx:P x) => (fun (y:A) => fun (Heq:eq x y) => ((eq_ind x (fun (__:A) => P __) Hx y Heq))).
Definition sym_eq : forall A, forall (x:A), forall (y:A), (eq x y) -> eq y x := fun (A:Type) => fun (x:A) => fun (y:A) => fun (Heq:eq x y) => (((((((rewrite_l) (A)) (x)) (fun (__:A) => eq __ x)) (refl x) y)) (((((((rewrite_l) (A)) (x)) (fun (__:A) => eq x __)) (refl x)) (y)) (Heq))).
Definition rewrite_r : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq y x) -> P y := fun (A:Type) => fun (x:A) => fun (P:A -> Prop) => fun (Hx:P x) => (fun (y:A) => fun (Heq:eq y x) => (((((eq_ind x) (fun (__:A) => P __)) (Hx)) (y)) (((((sym_eq) (A)) (y)) (x)) (Heq)))).
Definition eq_coerc : forall (A:Prop), forall (B:Prop), A -> (eq A B) -> B := fun (A:Prop) => fun (B:Prop) => fun (Ha:A) => (fun (Heq:eq A B) => ((((eq_ind A (fun (x_19:Prop) => x_19)) (Ha)) (B)) (Heq))).
Definition absurd : forall (A:Prop), A -> (C.Not A) -> C.False := fun (A:Prop) => fun (H:A) => (fun (Hn:C.Not A) => (((((C.Not_ind) (A)) (C.False)) (fun (_x_80:A -> C.False) => ((_x_80) (H)))) (Hn))).
Definition not_to_not : forall (A:Prop), forall (B:Prop), (A -> B) -> (C.Not B) -> C.Not A := fun (A:Prop) => fun (B:Prop) => fun (auto:A -> B) => (fun (auto':C.Not B) => (((C.nmk) (A)) (fun (auto'':A) => ((((absurd) (B)) ((auto) (auto''))) (auto'))))).
Definition sym_not_eq : forall A, forall (x:A), forall (y:A), (C.Not (eq x y)) -> C.Not (eq y x) := fun (A:Type) => fun (x:A) => fun (y:A) => fun (auto:C.Not (eq x y)) => (((C.nmk) (eq y x)) (fun (auto':eq y x) => ((((absurd) (eq x y)) (((((((rewrite_r) (A)) (x)) (fun (__:A) => eq x __)) (refl x)) (y)) (auto'))) (auto)))).
End Logic_make.

Module Coq_logic <: Logic_Type Coq_connectives := Logic_make Coq_connectives.

