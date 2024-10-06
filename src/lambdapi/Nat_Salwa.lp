// STTFA
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

// Connectives
constant symbol True : ηₚ (p bool);
constant symbol False : ηₚ (p bool);
constant symbol ¬
  : ηₚ (p (arrow bool bool));
constant symbol ∧
  : ηₚ
    (p (arrow bool (arrow bool bool)));
constant symbol v
  : ηₚ
    (p (arrow bool (arrow bool bool)));
notation v infix 6;    
constant symbol ∃
  : ηₚ
    (∀ₖ
     (λ (A : t),
        p (arrow (arrow A bool) bool)));
constant symbol equal
  : ηₚ
    (∀ₖ
     (λ (A : t),
        p (arrow A (arrow A bool))));


constant symbol I : ϵ True;
constant symbol falsity
  : ϵ
    (∀ bool
     (λ (t : ηₚ (p bool)), impl False t));
constant symbol nmk
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        impl (impl A False) (¬ A)));
constant symbol ¬-ind
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (Q : ηₚ (p bool)),
           impl (impl (impl A False) Q)
           (impl (¬ A) Q))));
constant symbol conj
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           impl A (impl B (∧ A B)))));
constant symbol match_and_prop
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           ∀ bool
           (λ (return : ηₚ (p bool)),
              impl (impl A (impl B return))
              (impl (∧ A B) return)))));
constant symbol or_introl
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)), impl A (A v B))));
constant symbol or_intror
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)), impl B (A v B))));
constant symbol match_or_prop
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           ∀ bool
           (λ (return : ηₚ (p bool)),
              impl (impl A return)
              (impl (impl B return) (impl (A v B) return))))));
constant symbol ex_intro
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ (arrow A bool)
        (λ (P : ηₚ (p (arrow A bool))),
           ∀ A
           (λ (x : ηₚ (p A)), impl (P x) (∃ A P)))));
constant symbol match_ex_prop
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ (arrow A bool)
        (λ (P : ηₚ (p (arrow A bool))),
           ∀ bool
           (λ (return : ηₚ (p bool)),
              impl
              (∀ A
               (λ (x : ηₚ (p A)), impl (P x) return))
              (impl (∃ A P) return)))));
constant symbol equal_refl
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A (λ (x : η A), equal A x x)));
constant symbol equal_leibniz
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : η A),
           ∀ A
           (λ (y : η A),
              impl (equal A x y)
              (∀ (arrow A bool)
               (λ (P : η (arrow A bool)),
                  impl (P x) (P y)))))));

constant symbol equal_ind [a] (x y : η a) : ϵ (equal a x y) → Π p, ϵ (p y) → ϵ (p x);

builtin "P"     ≔ ϵ;
builtin "T"     ≔ η;
builtin "eq"    ≔ equal;
builtin "refl"  ≔ equal_refl;
builtin "eqind" ≔ equal_ind;



// Natural numbers
constant symbol nat : t;
constant symbol O : ηₚ (p nat);
constant symbol S : ηₚ (p (arrow nat nat));

symbol = ≔ equal nat;
notation = infix 5;

//debug +t;
// Induction principle on natural numbers
constant symbol nat_ind
  : ϵ
    (∀ (arrow nat bool)
     (λ (Q : ηₚ (p (arrow nat bool))),
        impl (Q O)
        (impl
         (∀ nat
          (λ (x : ηₚ (p nat)), impl (Q x) (Q (S x))))
         (∀ nat (λ (x : ηₚ (p  nat)), Q x)))));


// Induction principle on natural numbers
/*symbol nat_ind (Q : ηₚ (p (arrow nat bool))) (case-zero : ϵ (Q O)) (case-succ : ϵ (∀ nat (λ (x : ηₚ (p nat)), (imp (Q x) (Q (S x)))))) (n : ηₚ (p nat)) : ϵ (Q n);
*/
// Discrimination principle for natural numbers
symbol nat_discr (n : ηₚ (p nat)) : ϵ ((n = O) v (∃ nat (λ m, (n = S m))));

// Definition of addition for natural numbers
symbol + (n m : ηₚ (p nat)) : ηₚ (p nat);
notation + infix right 10;
rule O + $y ↪ $y
with S $x + $y ↪ S ($x + $y);

compute S (S O) + S (S (S O));
type (λ x, ϵ ((x + O) = O));

// Lemmas for addition
symbol plus_O_r : Π (n : ηₚ (p nat)), ϵ ((n + O) = n) ≔
begin
  assume n;
  refine nat_ind (λ z, (z + O) = z) _ _ n
  {
    simplify;
    reflexivity;
  }
  {
    assume m IHm;
    simplify;
    rewrite IHm;
    reflexivity
  }
end;

symbol plus_S_r : Π (n m : ηₚ (p nat)), ϵ ((n + S m) = S (n + m)) ≔
begin
  assume n m;
  refine nat_ind (λ x , (x + S m) = S (x + m)) _ _ n 
  {
    simplify;
    reflexivity;
  }
  {
    assume n' IHn';
    simplify;
    rewrite IHn';
    reflexivity
  }
end;

symbol plus_comm : Π (n m : ηₚ (p nat)), ϵ ((n + m) = (m + n)) ≔
begin
  assume n m;
  refine nat_ind (λ x, (x + m) = (m + x)) _ _ n 
  {
    simplify;
    rewrite (plus_O_r m);
    reflexivity
  }
  {
    assume n' IHn';
    simplify;
    rewrite (plus_S_r m n');
    rewrite IHn';
    reflexivity;
  }
end;