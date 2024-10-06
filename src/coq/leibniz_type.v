Module Type Leibniz_Type.
Definition leibniz : forall (A:Type), A -> A -> Prop := fun (A:Type) => fun (x:A) => fun (y:A) => forall (P:(A -> Prop)), (P x) -> P y.
Axiom sym_leibniz : forall A, forall (x:A), forall (y:A), (leibniz (A) x y) -> leibniz (A) y x.
End Leibniz_Type.