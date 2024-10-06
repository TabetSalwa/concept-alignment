Require Import connectives_type.
Require Import logic_type.
Require Import relations_type.
Require Import connectives_coq.
Require Import logic_coq.

Module Relations_make (C : Connectives_Type) (G : Logic_Type (C)) <: (Relations_Type C G).
Definition reflexive : forall (A:Type), (A -> A -> Prop) -> Prop := 
 fun (A:Type) => fun (R:(A -> A -> Prop)) => forall (x:A), R x x.
Definition transitive : forall (A:Type), (A -> A -> Prop) -> Prop := 
 fun (A:Type) => fun (R:(A -> A -> Prop)) => forall (x:A), forall (y:A), forall (z:A), (R x y) -> (R y z) -> R x z.
Definition RC : forall (A:Type), (A -> A -> Prop) -> A -> A -> Prop := 
 fun (A:Type) => fun (R:(A -> A -> Prop)) => fun (x:A) => fun (y:A) => C.Or (R x y) (G.eq (A) x y).
Definition RC_reflexive : forall A, forall (R:(A -> A -> Prop)), reflexive (A) (RC (A) R) := 
 fun (A:Type) => fun (R:A -> A -> Prop) => fun (x:A) => (((C.or_intror) (R x x)) (G.eq (A) x x)) (((G.refl) (A)) (x)).
Definition injective : forall (A:Type), forall (B:Type), (A -> B) -> Prop := 
 fun (A:Type) => fun (B:Type) => fun (f:(A -> B)) => forall (x:A), forall (y:A), (G.eq (B) (f x) (f y)) -> G.eq (A) x y.
Definition commutative : forall (A:Type), (A -> A -> A) -> Prop := 
 fun (A:Type) => fun (f:(A -> A -> A)) => forall (x:A), forall (y:A), G.eq (A) (f x y) (f y x).
Definition associative : forall (A:Type), (A -> A -> A) -> Prop := 
 fun (A:Type) => fun (f:(A -> A -> A)) => forall (x:A), forall (y:A), forall (z:A), G.eq (A) (f (f x y) z) (f x (f y z)).
Definition monotonic : forall (A:Type), (A -> A -> Prop) -> (A -> A) -> Prop := 
 fun (A:Type) => fun (R:(A -> A -> Prop)) => fun (f:(A -> A)) => forall (x:A), forall (y:A), (R x y) -> R (f x) (f y).
End Relations_make.

Module Coq_relations := Relations_make Coq_connectives Coq_logic.


