Require Import connectives_type.

Module Coq_connectives <: Connectives_Type.
Definition True := True.
Definition False := False.
Definition Not := not.
Definition Or := or.
Definition equal {A} := @eq A.
Definition I := Logic.I.
Definition falsity := fun (t : Prop) (False : False) => False_ind t False.
Definition nmk := fun (P : Prop) (notP : P -> False) => notP.
Definition Not_ind := fun (A Q : Prop) (H : (A -> False) -> Q) (notA : Not A) => H notA.
Definition or_introl := or_introl.
Definition or_intror := or_intror.
Definition match_Or_prop := or_ind.
Definition equal_refl {A} := @eq_refl A.
Definition equal_leibniz := fun (A : Type) (x y : A) (e : equal x y) (P : A -> Prop) (Px : P x) =>
eq_ind x P Px y e.
End Coq_connectives.