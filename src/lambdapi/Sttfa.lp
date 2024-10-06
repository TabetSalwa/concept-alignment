/* Simple type theory with prenex polymorphism */

constant symbol t : TYPE;
constant symbol arrow : t → t → t;
constant symbol bool : t;
symbol η : (t → TYPE);
constant symbol ptype : TYPE;
constant symbol p : t → ptype;
symbol ηₚ : ptype → TYPE;
constant symbol ∀ₖ : (t → ptype) → ptype;
symbol ϵ : (η bool) → TYPE;
constant symbol impl : η bool → η bool → η bool;
constant symbol ∀ (T : t) : (η T → η bool) → η bool;
constant symbol ∀ₚ : (t → η bool) → η bool;

rule η ↪ λ t, ηₚ (p t);
rule ηₚ (p (arrow $l $r)) ↪ η $l → η $r;
rule ηₚ (∀ₖ $f) ↪ Π x : t, ηₚ ($f x);
rule ϵ (∀ $T $f) ↪ Π (x : η $T), ϵ ($f x);
rule ϵ (impl $l $r) ↪ ϵ $l → ϵ $r;
rule ϵ (∀ₚ $f) ↪ Π (x : t), ϵ ($f x);


