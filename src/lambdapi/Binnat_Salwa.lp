
require open Concepts.Logic_Type;

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

// Logic
constant symbol eq
  : ηₚ
    (∀ₖ
     (λ (A : t),
        p (arrow A (arrow A bool))));
constant symbol refl
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A (λ (x : ηₚ (p A)), eq A x x)));
constant symbol eq_ind
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ (arrow A bool)
           (λ (P : ηₚ (p (arrow A bool))),
              impl (P x)
              (∀ A
               (λ (y : ηₚ (p A)), impl (eq A x y) (P y)))))));
symbol eq_rect_r
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (a : ηₚ (p A)),
           ∀ A
           (λ (x : ηₚ (p A)),
              impl (eq A x a)
              (∀ (arrow A bool)
               (λ (P : ηₚ (p (arrow A bool))),
                  impl (P a) (P x)))))))
  ≔ λ (A : t),
        λ (a : ηₚ (p A)),
          λ (x : ηₚ (p A)),
            λ (p1 : ϵ (eq A x a)),
              eq_ind A x
              (λ (y : ηₚ (p A)),
                 ∀ (arrow A bool)
                 (λ (P : ηₚ (p (arrow A bool))),
                    impl (P y) (P x)))
              (λ (P : ηₚ (p (arrow A bool))),
                 λ (auto : ϵ (P x)), auto)
              a p1;
symbol eq_ind_r
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (a : ηₚ (p A)),
           ∀ (arrow A bool)
           (λ (P : ηₚ (p (arrow A bool))),
              impl (P a)
              (∀ A
               (λ (x : ηₚ (p A)), impl (eq A x a) (P x)))))))
  ≔ λ (A : t),
        λ (a : ηₚ (p A)),
          λ (P : ηₚ (p (arrow A bool))),
            λ (p1 : ϵ (P a)),
              λ (x0 : ηₚ (p A)),
                λ (p0 : ϵ (eq A x0 a)),
                  eq_rect_r A a x0 p0
                  (λ (x1 : ηₚ (p A)), P x1) p1;
symbol rewrite_l
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ (arrow A bool)
           (λ (P : ηₚ (p (arrow A bool))),
              impl (P x)
              (∀ A
               (λ (y : ηₚ (p A)), impl (eq A x y) (P y)))))))
  ≔ λ (A : t),
        λ (x : ηₚ (p A)),
          λ (P : ηₚ (p (arrow A bool))),
            λ (Hx : ϵ (P x)),
              λ (y : ηₚ (p A)),
                λ (Heq : ϵ (eq A x y)),
                  eq_ind A x (λ (__ : ηₚ (p A)), P __) Hx y
                  Heq;
symbol sym_eq
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ A
           (λ (y : ηₚ (p A)), impl (eq A x y) (eq A y x)))))
  ≔ λ (A : t),
        λ (x : ηₚ (p A)),
          λ (y : ηₚ (p A)),
            λ (Heq : ϵ (eq A x y)),
              rewrite_l A x (λ (__ : ηₚ (p A)), eq A __ x)
              (refl A x) y
              (rewrite_l A x (λ (__ : ηₚ (p A)), eq A x __)
               (refl A x) y Heq);
symbol rewrite_r
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ (arrow A bool)
           (λ (P : ηₚ (p (arrow A bool))),
              impl (P x)
              (∀ A
               (λ (y : ηₚ (p A)), impl (eq A y x) (P y)))))))
  ≔ λ (A : t),
        λ (x : ηₚ (p A)),
          λ (P : ηₚ (p (arrow A bool))),
            λ (Hx : ϵ (P x)),
              λ (y : ηₚ (p A)),
                λ (Heq : ϵ (eq A y x)),
                  eq_ind A x (λ (__ : ηₚ (p A)), P __) Hx y
                  (sym_eq A y x Heq);
symbol eq_coerc
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           impl A (impl (eq bool A B) B))))
  ≔ λ (A : ηₚ (p bool)),
        λ (B : ηₚ (p bool)),
          λ (Ha : ϵ A),
            λ (Heq : ϵ (eq bool A B)),
              eq_ind bool A
              (λ (x_19 : ηₚ (p bool)), x_19) Ha B Heq;
symbol trans_eq
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ A
           (λ (y : ηₚ (p A)),
              ∀ A
              (λ (z : ηₚ (p A)),
                 impl (eq A x y) (impl (eq A y z) (eq A x z)))))))
  ≔ λ (A : t),
        λ (x : ηₚ (p A)),
          λ (y : ηₚ (p A)),
            λ (z : ηₚ (p A)),
              λ (H1 : ϵ (eq A x y)),
                λ (H2 : ϵ (eq A y z)),
                  eq_ind_r A y (λ (x0 : ηₚ (p A)), eq A x0 z)
                  (rewrite_l A x
                   (λ (__ : ηₚ (p A)), eq A __ z)
                   (rewrite_l A x
                    (λ (__ : ηₚ (p A)), eq A x __) (refl A x)
                    z
                    (rewrite_r A y
                     (λ (__ : ηₚ (p A)), eq A __ z) H2 x H1))
                   y H1)
                  x H1;
symbol eq_f
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ₚ
        (λ (B : t),
           ∀ (arrow A B)
           (λ (f : ηₚ (p (arrow A B))),
              ∀ A
              (λ (x : ηₚ (p A)),
                 ∀ A
                 (λ (y : ηₚ (p A)),
                    impl (eq A x y) (eq B (f x) (f y))))))))
  ≔ λ (A : t),
        λ (B : t),
          λ (f : ηₚ (p (arrow A B))),
            λ (x : ηₚ (p A)),
              λ (y : ηₚ (p A)),
                λ (H : ϵ (eq A x y)),
                  eq_ind_r A y
                  (λ (x0 : ηₚ (p A)), eq B (f x0) (f y))
                  (rewrite_l A x
                   (λ (__ : ηₚ (p A)), eq B (f __) (f y))
                   (rewrite_l A x
                    (λ (__ : ηₚ (p A)), eq B (f x) (f __))
                    (refl B (f x)) y H)
                   y H)
                  x H;
symbol eq_f2
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ₚ
        (λ (B : t),
           ∀ₚ
           (λ (C : t),
              ∀ (arrow A (arrow B C))
              (λ
                 (f : ηₚ (p (arrow A (arrow B C)))),
                 ∀ A
                 (λ (x1 : ηₚ (p A)),
                    ∀ A
                    (λ (x2 : ηₚ (p A)),
                       ∀ B
                       (λ (y1 : ηₚ (p B)),
                          ∀ B
                          (λ (y2 : ηₚ (p B)),
                             impl (eq A x1 x2)
                             (impl (eq B y1 y2)
                              (eq C (f x1 y1) (f x2 y2))))))))))))
  ≔ λ (A : t),
        λ (B : t),
          λ (C : t),
            λ (f : ηₚ (p (arrow A (arrow B C)))),
              λ (x1 : ηₚ (p A)),
                λ (x2 : ηₚ (p A)),
                  λ (y1 : ηₚ (p B)),
                    λ (y2 : ηₚ (p B)),
                      λ (E1 : ϵ (eq A x1 x2)),
                        λ (E2 : ϵ (eq B y1 y2)),
                          eq_ind_r A x2
                          (λ (x : ηₚ (p A)),
                             eq C (f x y1) (f x2 y2))
                          (eq_ind_r B y2
                           (λ (x : ηₚ (p B)),
                              eq C (f x2 x) (f x2 y2))
                           (rewrite_l A x1
                            (λ (__ : ηₚ (p A)),
                               eq C (f __ y2) (f x2 y2))
                            (rewrite_l B y1
                             (λ (__ : ηₚ (p B)),
                                eq C (f x1 __) (f x2 y2))
                             (rewrite_l A x1
                              (λ (__ : ηₚ (p A)),
                                 eq C (f x1 y1) (f __ y2))
                              (rewrite_l B y1
                               (λ (__ : ηₚ (p B)),
                                  eq C (f x1 y1) (f x1 __))
                               (refl C (f x1 y1)) y2 E2)
                              x2 E1)
                             y2 E2)
                            x2 E1)
                           y1 E2)
                          x1 E1;
symbol absurd
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        impl A (impl (¬ A) False)))
  ≔ λ (A : ηₚ (p bool)),
        λ (H : ϵ A),
          λ (Hn : ϵ (¬ A)),
            ¬-ind A False
            (λ (_x_80 : ϵ (impl A False)), _x_80 H)
            Hn;
symbol not_to_not
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           impl (impl A B)
           (impl (¬ B) (¬ A)))))
  ≔ λ (A : ηₚ (p bool)),
        λ (B : ηₚ (p bool)),
          λ (auto : ϵ (impl A B)),
            λ (auto' : ϵ (¬ B)),
              nmk A
              (λ (auto'' : ϵ A), absurd B (auto auto'') auto');
symbol sym_not_eq
  : ϵ
    (∀ₚ
     (λ (A : t),
        ∀ A
        (λ (x : ηₚ (p A)),
           ∀ A
           (λ (y : ηₚ (p A)),
              impl (¬ (eq A x y))
              (¬ (eq A y x))))))
  ≔ λ (A : t),
        λ (x : ηₚ (p A)),
          λ (y : ηₚ (p A)),
            λ (auto : ϵ (¬ (eq A x y))),
              nmk (eq A y x)
              (λ (auto' : ϵ (eq A y x)),
                 absurd (eq A x y)
                 (rewrite_r A x (λ (__ : ηₚ (p A)), eq A x __)
                  (refl A x) y auto')
                 auto);
symbol proj1
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           impl (∧ A B) A)))
  ≔ λ (A : ηₚ (p bool)),
        λ (B : ηₚ (p bool)),
          λ (AB : ϵ (∧ A B)),
            match_and_prop A B A
            (λ (_x_120 : ϵ A), λ (_x_119 : ϵ B), _x_120) AB;
symbol proj2
  : ϵ
    (∀ bool
     (λ (A : ηₚ (p bool)),
        ∀ bool
        (λ (B : ηₚ (p bool)),
           impl (∧ A B) B)))
  ≔ λ (A : ηₚ (p bool)),
        λ (B : ηₚ (p bool)),
          λ (AB : ϵ (∧ A B)),
            match_and_prop A B B
            (λ (_x_120 : ϵ A), λ (_x_119 : ϵ B), _x_119) AB;
symbol decidable : ηₚ (p (arrow bool bool))
  ≔ λ (A : ηₚ (p bool)),
         A v (¬ A);


////////////////////
//Positive numbers//
////////////////////
/*symbol prop : ηₚ (p bool);
builtin "Prop" ≔ prop;

inductive positive : TYPE ≔
| xH : positive
| xI : positive → positive
| xO : positive → positive;*/

symbol positive : t;
symbol xH : ηₚ (p positive);
symbol xO : ηₚ (p (arrow positive positive));
symbol xI : ηₚ (p (arrow positive positive));

//Boolean functions for testing head constructor
/*symbol is_xH : ηₚ (p (arrow positive bool));
rule is_xH xH ↪ True;
rule is_xH (xO $p) ↪ False;
rule is_xH (xI $p) ↪ False;

symbol is_xO : ηₚ (p (arrow positive bool));
rule is_xO xH ↪ False;
rule is_xO (xO $p) ↪ True;
rule is_xO (xI $p) ↪ False;

symbol is_xI : ηₚ (p (arrow positive bool));
rule is_xI xH ↪ False;
rule is_xI (xO $p) ↪ False;
rule is_xI (xI $p) ↪ True;*/

//Successor function on positives
symbol succ : ηₚ (p (arrow positive positive));
rule succ xH ↪ xO xH;
rule succ (xO $pos) ↪ xI $pos;
rule succ (xI $pos) ↪ xO (succ $pos);

// Discriminate constructors
/*symbol xI_isnot_xH [x] : ϵ (¬ (equal positive (xI x) xH)) ≔
begin
  assume x;
  apply nmk (equal positive (xI x) xH);
  assume H;
  refine @equal_ind positive (xI x) xH H (λ z, is_xH z) _;
  simplify;
  apply I;
end;

symbol xO_isnot_xH [x] : ϵ (¬ (equal positive (xO x) xH)) ≔
begin
  assume x;
  apply nmk (equal positive (xO x) xH);
  assume H;
  refine @equal_ind positive (xO x) xH H (λ z, is_xH z) _;
  simplify;
  apply I;
end;

symbol xI_isnot_xO [x y] : ϵ (¬ (equal positive (xI x) (xO y))) ≔
begin
  assume x y;
  apply nmk (equal positive (xI x) (xO y));
  assume H;
  refine @equal_ind positive (xI x) (xO y) H (λ z, is_xO z) _;
  simplify;
  apply I;
end;
*/
//Induction principle on positive numbers
/*symbol pos_ind 
  : ϵ
  (∀ (arrow positive bool)
   (λ (Q : ηₚ (p (arrow positive bool))),
      impl (Q xH)
      (impl
       (∀ positive
        (λ (x : ηₚ (p positive)), impl (Q x) (Q (succ x))))
       (∀ positive (λ (x : ηₚ (p  positive)), Q x)))));
*/

symbol pos_ind :
  ϵ
    (∀ (arrow positive bool)
      (λ (Q : ηₚ (p (arrow positive bool))),
        impl (Q xH)
          (impl (∀ positive 
            (λ (z : ηₚ (p positive)), impl (Q z) (Q (xI z))))
              (impl (∀ positive
                (λ (y : ηₚ (p positive)), impl (Q y) (Q (xO y))))
                  (∀ positive (λ (x : ηₚ (p positive)), Q x))
              )
          )
      )
    );

//Addition on positive numbers
symbol plus (p1 p2 : ηₚ (p positive)) (carry : ηₚ (p bool)) : ηₚ (p positive);
rule plus (xI $p1) (xI $p2) False ↪ xO (plus $p1 $p2 True)
with plus (xI $p1) (xO $p2) False ↪ xI (plus $p1 $p2 False)
with plus (xI $p1) xH False ↪ xO (succ $p1)
with plus (xO $p1) (xI $p2) False ↪ xI (plus $p1 $p2 False)
with plus (xO $p1) (xO $p2) False ↪ xO (plus $p1 $p2 False)
with plus (xO $p1) xH False ↪ xI $p1
with plus xH (xI $p2) False ↪ xO (succ $p2)
with plus xH (xO $p2) False ↪ xI $p2 
with plus xH xH False ↪ xO xH
with plus (xI $p1) (xI $p2) True ↪ xI (plus $p1 $p2 True)
with plus (xI $p1) (xO $p2) True ↪ xO (plus $p1 $p2 True)
with plus (xI $p1) xH True ↪ xI (succ $p1)
with plus (xO $p1) (xI $p2) True ↪ xO (plus $p1 $p2 True)
with plus (xO $p1) (xO $p2) True ↪ xI (plus $p1 $p2 False)
with plus (xO $p1) xH True ↪ xO (succ $p1)
with plus xH (xI $p2) True ↪ xI (succ $p2)
with plus xH (xO $p2) True ↪ xO (succ $p2)
with plus xH xH True ↪ xI xH;

/*symbol plus_one (x : ηₚ (p positive)) : ϵ (equal positive (plus xH x False) (succ x)) ≔
begin
  assume x;
  refine pos_ind (λ z, equal positive (plus xH z False) (succ z)) _ _ _ x
  {
    simplify;
    reflexivity;
  }
  {
    assume z Hz;
    simplify;
    reflexivity;
  }
  {
    assume z Hz;
    simplify;
    reflexivity
  }
end;
    
symbol plus_two (x : ηₚ (p positive)) : ϵ (equal positive (plus (xO xH) x False) (succ (succ x))) ≔
begin
  assume x;
  refine pos_ind (λ z, equal positive (plus (xO xH) z False) (succ (succ z))) _ _ _ x
  {
    simplify;
    reflexivity;
  }
  {
    assume z Hz;
    simplify;
    rewrite plus_one z;
    reflexivity;
  }
  {
    assume z Hz;
    simplify;
    rewrite plus_one z;
    reflexivity
  }
end;
*/


/////////////////////////////////////////////////
//Binary natural numbers using positive numbers//
/////////////////////////////////////////////////
symbol binnat : t;
symbol O : ηₚ (p binnat);
symbol S : ηₚ (p (arrow binnat binnat));

symbol = ≔ equal binnat;
notation = infix 5;

//Boolean functions for testing head constructor
/*symbol is_O : ηₚ (p (arrow binnat bool));
rule is_O O ↪ True;
rule is_O S $n ↪ False;

symbol is_S : ηₚ (p (arrow binnat bool));
rule is_S O ↪ False;
rule is_S (S $n) ↪ True;*/

//Induction principle on binary natural numbers à la Peano
symbol binnat_ind
  : ϵ
    (∀ (arrow binnat bool)
     (λ (Q : ηₚ (p (arrow binnat bool))),
        impl (Q O)
        (impl
         (∀ binnat
          (λ (x : ηₚ (p binnat)), impl (Q x) (Q (S x))))
         (∀ binnat (λ (x : ηₚ (p  binnat)), Q x)))));


symbol binnat_discr (n : ηₚ (p binnat)) : ϵ ((equal binnat n O) v (∃ binnat (λ m, equal binnat n (S m)))) ≔
begin
  assume n;
  refine binnat_ind (λ x, (equal binnat x O) v (∃ binnat (λ y, equal binnat x (S y)))) _ _ n
  {
    apply or_introl (equal binnat O O) (∃ binnat (λ y, equal binnat O (S y)));
    reflexivity;
  }
  {
    assume m IHn;
    apply or_intror (equal binnat (S m) O) (∃ binnat (λ y, equal binnat (S m) (S y)));
    apply ex_intro binnat (λ y, equal binnat (S m) (S y)) m;
    reflexivity
  }
end;

symbol to_binnat : ηₚ (p (arrow positive binnat));
rule S O ↪ to_binnat xH;
rule S (to_binnat $pos) ↪ to_binnat (succ $pos);

symbol to_pos : ηₚ (p (arrow binnat positive));
rule to_pos (to_binnat $x) ↪ $x;

/*symbol S_isnot_O (n : ηₚ (p binnat)): ϵ (¬ (equal binnat O (S n))) ≔
begin
  assume n;
  apply nmk (equal binnat O (S n));
  assume H;
  refine @equal_ind binnat (O) (S n) H (λ z, is_S z) _ ;
  simplify;
  apply I;
end;

symbol to_pos_S : Π (n : ηₚ (p binnat)), ϵ (impl (is_S n) (to_binnat (to_pos n) = n)) ≔
begin
  assume n Hn;
  refine binnat_ind (λ x, (to_binnat (to_pos x) = x)) _ _ n 
  {
    
  }
  {

  }
end;

symbol to_pos_binnat : Π (n : ηₚ (p binnat)), ϵ (impl (¬ (n = O)) (to_binnat (to_pos n) = n)) ≔
begin
  assume n H;
  refine binnat_ind (λ z, to_binnat (to_pos z) = z) _ _ n 
  {
    apply nmk (O = O) H
    {}
    {}
  }
  {
    assume m IHm;
    simplify;
  }
end;

*/


/*symbol + (n m : ηₚ (p binnat)) : ηₚ (p binnat);
notation + infix right 10;
rule O + $y ↪ $y
with (to_binnat $pos) + O ↪ (to_binnat $pos)
with (S $x) + (to_binnat $pos) ↪ to_binnat (plus (to_pos (S $x)) ($pos) False) 
with (to_binnat $pos) + (S $y) ↪ to_binnat (plus $pos (to_pos (S $y)) False)
with (S $x) + (S $y) ↪ to_binnat (plus (to_pos (S $x)) (to_pos (S $y)) False)
with (to_binnat $p1) + (to_binnat $p2) ↪ to_binnat (plus $p1 $p2 False);*/

/*symbol + (n m : ηₚ (p binnat)) : ηₚ (p binnat);
notation + infix right 10;
rule O + $y ↪ $y
with (S $x) + $y ↪ S ($x + $y)
with (to_binnat (succ $p)) + $y ↪ S ((to_binnat $p) + $y);*/

symbol + (n m : ηₚ (p binnat)) : ηₚ (p binnat);
notation + infix right 10;
rule O + $y ↪ $y
with (to_binnat $pos) + O ↪ (to_binnat $pos)
/*with (S ($x + $y)) ↪ (to_binnat (succ (plus (to_pos $x) (to_pos $y) False)))*/
with (S $x) + $y ↪ S ($x + $y)
with (S $x) + (to_binnat $pos) ↪ to_binnat (plus (to_pos (S $x)) ($pos) False) 
with (to_binnat $pos) + (S $y) ↪ to_binnat (plus $pos (to_pos (S $y)) False)
with (S $x) + (S $y) ↪ to_binnat (plus (to_pos (S $x)) (to_pos (S $y)) False)
with (to_binnat $p1) + (to_binnat $p2) ↪ to_binnat (plus $p1 $p2 False);

symbol six ≔ S (S (S (S (S (S O))))); 
symbol five ≔ to_binnat (xI (xO xH));
compute (six + five);



