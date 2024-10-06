Require Import connectives_type.
Require Import leibniz_type.
Require Import logic_type.
Require Import relations_type.
Require Import bool_type.
Require Import connectives_coq.
Require Import leibniz_coq.
Require Import logic_coq.
Require Import relations_coq.

Module Bool_make (C : Connectives_Type) (L : Leibniz_Type) (G : Logic_Type C) (R : Relations_Type C G) <: Bool_Type C L G R.
Definition bool := bool.
Definition true := true.
Definition false := false.
Definition match_bool_prop := bool_ind.
Definition match_bool_type := 
 fun (ret : Type) (rt rf : ret) (z : bool) => if z then rt else rf.
Definition axiom_match_bool_type_true :=
 fun (ret : Type) (case_true case_false : ret) =>
 (C.equal_refl ret case_true : C.equal ret case_true case_true).
Definition eq_match_bool_type_true : forall (return_:Type), forall (case_true:return_), forall (case_false:return_), L.leibniz (return_) (match_bool_type (return_) case_true case_false true) case_true := 
 fun (return_:Type) => fun (case_true:return_) => fun (case_false:return_) => ((((C.equal_leibniz) (return_)) (match_bool_type (return_) case_true case_false true)) (case_true)) ((((axiom_match_bool_type_true) (return_)) (case_true)) (case_false)).
Definition axiom_match_bool_type_false :=
 fun (ret : Type) (case_true case_false : ret) =>
 (C.equal_refl ret case_false : C.equal ret case_false case_false).
Definition eq_match_bool_type_false : forall return_, forall (case_true:return_), forall (case_false:return_), L.leibniz (return_) (match_bool_type (return_) case_true case_false false) case_false := 
 fun (return_:Type) => fun (case_true:return_) => fun (case_false:return_) => ((((C.equal_leibniz) (return_)) (match_bool_type (return_) case_true case_false false)) (case_false)) ((((axiom_match_bool_type_false) (return_)) (case_true)) (case_false)).
Definition sym_eq_match_bool_type_true : forall return_, forall (case_true:return_), forall (case_false:return_), L.leibniz (return_) case_true (match_bool_type (return_) case_true case_false true) := 
 fun (return_:Type) => fun (case_true:return_) => fun (case_false:return_) => ((((L.sym_leibniz) (return_)) (match_bool_type (return_) case_true case_false true)) (case_true)) ((((eq_match_bool_type_true) (return_)) (case_true)) (case_false)).
Definition sym_eq_match_bool_type_false : forall return_, forall (case_true:return_), forall (case_false:return_), L.leibniz (return_) case_false (match_bool_type (return_) case_true case_false false) := 
 fun (return_:Type) => fun (case_true:return_) => fun (case_false:return_) => ((((L.sym_leibniz) (return_)) (match_bool_type (return_) case_true case_false false)) (case_false)) ((((eq_match_bool_type_false) (return_)) (case_true)) (case_false)).
Definition bool_discr : forall (x:bool), forall (y:bool), (G.eq (bool) x y) -> match_bool_type (Prop) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) y) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) y) x := 
 fun (x:bool) => fun (y:bool) => fun (Deq:G.eq (bool) x y) => (((((((G.eq_ind) (bool)) (x)) (fun (x_13:bool) => match_bool_type (Prop) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) x_13) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) x_13) x)) (((((match_bool_prop) (fun (__:bool) => match_bool_type (Prop) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) __) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) __) __)) ((((((sym_eq_match_bool_type_true) (Prop)) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) true)) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) true)) (fun (x0:Prop) => x0)) ((((((sym_eq_match_bool_type_true) (Prop)) (forall (P:Prop), P -> P)) (forall (P:Prop), P)) (fun (x0:Prop) => x0)) (fun (P:Prop) => fun (DH:P) => (DH))))) ((((((sym_eq_match_bool_type_false) (Prop)) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) false)) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) false)) (fun (x0:Prop) => x0)) ((((((sym_eq_match_bool_type_false) (Prop)) (forall (P:Prop), P)) (forall (P:Prop), P -> P)) (fun (x0:Prop) => x0)) (fun (P:Prop) => fun (DH:P) => (DH))))) (x))) (y)) (Deq)).
Definition not_eq_true_false : C.Not (G.eq (bool) true false) := 
 ((C.nmk) (G.eq (bool) true false)) (fun (Heq:G.eq (bool) true false) => (((((((eq_match_bool_type_false) (Prop)) (forall (P:Prop), P -> P)) (forall (P:Prop), P)) (fun (x:Prop) => x)) ((((((eq_match_bool_type_true) (Prop)) (match_bool_type (Prop) (forall (P:Prop), P -> P) (forall (P:Prop), P) false)) (match_bool_type (Prop) (forall (P:Prop), P) (forall (P:Prop), P -> P) false)) (fun (x:Prop) => x)) ((((bool_discr) (true)) (false)) (Heq)))) (C.False))).
Definition true_or_false : forall (b:bool), C.Or (G.eq (bool) b true) (G.eq (bool) b false) := 
 fun (b:bool) => ((((match_bool_prop) (fun (__:bool) => C.Or (G.eq (bool) __ true) (G.eq (bool) __ false))) ((((C.or_introl) (G.eq (bool) true true)) (G.eq (bool) true false)) (((G.refl) (bool)) (true)))) ((((R.RC_reflexive) (bool)) (fun (__:bool) => fun (_0:bool) => G.eq (bool) false true)) (false))) (b).
End Bool_make.

Module Coq_bool <: Bool_Type Coq_connectives Coq_leibniz Coq_logic Coq_relations := Bool_make Coq_connectives Coq_leibniz Coq_logic Coq_relations.
