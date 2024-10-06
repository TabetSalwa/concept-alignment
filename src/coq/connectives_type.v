Module Type Connectives_Type.
Parameter True : Prop.
Parameter False : Prop.
Parameter Not : Prop -> Prop.
Parameter Or : Prop -> Prop -> Prop.
Parameter equal : forall (A:Type), A -> A -> Prop.
Axiom I : True.
Axiom falsity : forall (t:Prop), False -> t.
Axiom nmk : forall (A:Prop), (A -> False) -> Not A.
Axiom Not_ind : forall (A:Prop), forall (Q:Prop), ((A -> False) -> Q) -> (Not A) -> Q.
Axiom or_introl : forall (A:Prop), forall (B:Prop), A -> Or A B.
Axiom or_intror : forall (A:Prop), forall (B:Prop), B -> Or A B.
Axiom match_Or_prop : forall (A:Prop), forall (B:Prop), forall (return_:Prop), (A -> return_) -> (B -> return_) -> (Or A B) -> return_.
Axiom equal_refl : forall A, forall (x:A), equal A x x.
Axiom equal_leibniz : forall A, forall (x:A), forall (y:A), (equal (A) x y) -> forall (P:(A -> Prop)), (P x) -> P y.
End Connectives_Type.