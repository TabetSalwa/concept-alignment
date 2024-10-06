Require Import leibniz_type.

Module Leibniz_make <: Leibniz_Type.
Definition leibniz {A} (u v : A) :=
 forall P : A -> Prop, P u -> P v.
Definition refl_leibniz {A} (a : A) : leibniz a a :=
 fun (P : A -> Type) (H : P a) => H.
Definition sym_leibniz {A} (u v : A) (e : leibniz u v) : leibniz v u :=
 fun (P : A -> Prop) => e (fun x => P x -> P u) (refl_leibniz u P).
End Leibniz_make.

Module Coq_leibniz <: Leibniz_Type := Leibniz_make.