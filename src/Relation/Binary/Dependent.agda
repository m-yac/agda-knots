
module Relation.Binary.Dependent where

open import Relation.Binary using (Rel; REL; IsEquivalence) public
open import Data.Product
open import Level

open IsEquivalence {{...}}


-- Dependent n-ary operations

Op₀ : ∀ {ℓa} (A : Set ℓa) -> Set ℓa
Op₀ A = A

2-Op₀ : ∀ {ℓa ℓb} (A : Set ℓa) (B : A -> A -> Set ℓb) -> Set (ℓa ⊔ ℓb)
2-Op₀ A B = ∀ (a : A) -> B a a

2-Op₁ : ∀ {ℓa ℓb} (A : Set ℓa) (B : A -> A -> Set ℓb) -> Set (ℓa ⊔ ℓb)
2-Op₁ A B = ∀ {a b : A} -> B a b -> B a b

2-Op₂ : ∀ {ℓa ℓb} (A : Set ℓa) (B : A -> A -> Set ℓb) -> Set (ℓa ⊔ ℓb)
2-Op₂ A B = ∀ {a b c : A} -> B a b -> B b c -> B a c


-- A relation on a relation on a set, respecting some other relation on that set (phew!)
-- This equality is defined on x : B a b and y : B a' b' only when we have a proof that a ∼ a' and b ∼ b'
Rel-on : ∀ {ℓa ℓb ℓ₁} {A : Set ℓa} (~ : Rel A ℓ₁) (B : Rel A ℓb) -> (ℓ₂ : Level) -> Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ suc ℓ₂)
Rel-on _∼_ B ℓ₂ = ∀ {a a' b b'} -> B a b -> B a' b' -> a ∼ a' -> b ∼ b' -> Set ℓ₂

-- If ∼ is an equivalence, we can define a notion of dependent equivalence:
record IsEquivalenceOn {ℓa ℓb ℓ₁ ℓ₂} {A : Set ℓa} {_∼_ : Rel A ℓ₁} {{isEquiv : IsEquivalence _∼_}}
                       (B : Rel A ℓb) (_≈_by_,_ : Rel-on _∼_ B ℓ₂) : Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    refl-on  : ∀ {a b} {x : B a b} (p₁ : a ∼ a) (p₂ : b ∼ b)
               -> x ≈ x by p₁ , p₂
    sym-on   : ∀ {a b a' b'} {x : B a b} {y : B a' b'}
               -> (p₁ : a ∼ a') (p₂ : b ∼ b')
               -> x ≈ y by p₁ , p₂ -> y ≈ x by (sym p₁) , (sym p₂)
    trans-on : ∀ {a b a' b' a'' b''} {x : B a b} {y : B a' b'} {z : B a'' b''}
               -> (p₁ : a ∼ a') (p₁' : a' ∼ a'') (p₂ : b ∼ b') (p₂' : b' ∼ b'')
               -> x ≈ y by p₁ , p₂ -> y ≈ z by p₁' , p₂'
               -> x ≈ z by (trans p₁ p₁') , (trans p₂ p₂')


-- A heterogenous relation on a relation on a set
REL-on : ∀ {ℓa ℓb} (A : Set ℓa) (B : Rel A ℓb) -> (ℓ : Level) -> Set _
REL-on A B ℓ = ∀ {a a' b b'} -> B a b -> B a' b' -> Set ℓ

module Heterogenous {ℓa ℓb ℓ₁ ℓ₂} (A : Set ℓa) (_∼_ : Rel A ℓ₁) (B : Rel A ℓb)
                    (_≈_by_,_ : Rel-on _∼_ B ℓ₂) where

  -- The natural heterogenous relation arising from any Rel-on:
  -- For x : B a b and y : B a' b', a proof of x ≈ y is exactly a proof
  --  that a ∼ a' (p₁), b ∼ b' (p₂), and x ≈ y by p₁ , p₂
  infix 2 _≈_
  _≈_ : REL-on A B (ℓ₁ ⊔ ℓ₂)
  x ≈ y = ∃[ p₁ ] ∃[ p₂ ] (x ≈ y by p₁ , p₂)

  -- A proof of x ≈ y by p₁ , p₂ gives us a proof that x ≈ y
  wrap : ∀ {a a' b b' : A} {x : B a b} {y : B a' b'} {p₁ : a ∼ a'} {p₂ : b ∼ b'}
         -> x ≈ y by p₁ , p₂ -> x ≈ y
  wrap {p₁ = p₁} {p₂} pf = p₁ , p₂ , pf

  -- A proof of x ≈ y gives us some p₁ and p₂ such that x ≈ y by p₁ , p₂
  unwrap : ∀ {a a' b b' : A} {x : B a b} {y : B a' b'}
           -> (ps : x ≈ y) -> x ≈ y by (proj₁ ps) , (proj₁ (proj₂ ps))
  unwrap (_ , _ , pf) = pf

  -- If _≈_by_,_ is an equivalence on ∼, _≈_ is a heterogenous equivalence relation
  module HeterogenousEquivalenceOn {{isEquiv : IsEquivalence _∼_}}
                                   {{isEquivOn : IsEquivalenceOn {{isEquiv}} B _≈_by_,_}} where

    module Homog = IsEquivalenceOn isEquivOn

    refl-on : ∀ {a b} {x : B a b} -> x ≈ x
    refl-on = wrap (Homog.refl-on (refl {{isEquiv}}) refl)

    sym-on : ∀ {a a' b b'} {x : B a b} {y : B a' b'}
             -> x ≈ y -> y ≈ x
    sym-on ( p₁ , p₂ , pf ) = wrap (Homog.sym-on p₁ p₂ pf)
    
    trans-on : ∀ {a a' a'' b b' b''} {x : B a b} {y : B a' b'} {z : B a'' b''}
               -> x ≈ y -> y ≈ z -> x ≈ z
    trans-on ( p₁ , p₂ , pf ) ( p₁' , p₂' , pf' ) = wrap (Homog.trans-on p₁ p₁' p₂ p₂' pf pf')

    import Relation.Binary.PropositionalEquality as Eq

    ≡-to-≈ : ∀ {a b} {x : B a b} {y : B a b} -> x Eq.≡ y -> x ≈ y
    ≡-to-≈ Eq.refl = refl-on

  -- The notion of an operation being preserved by ≈
  
  Congruent₀-on : (e : 2-Op₀ A B) -> Set _
  Congruent₀-on e = ∀ (a a') -> a ∼ a' -> e a ≈ e a'

  Congruent₂-on : (∙ : 2-Op₂ A B) -> Set _
  Congruent₂-on _∙_ = ∀ {a a' b b' c c'} {x : B a b} {y : B a' b'} {u : B b c} {v : B b' c'}
                      -> x ≈ y -> u ≈ v -> (x ∙ u) ≈ (y ∙ v)


-- Building dependent equivalences from families of equivalences on B

IsPointwiseEquivalence : ∀ {ℓa ℓb ℓ} {A : Set ℓa} (B : Rel A ℓb) (_∼_ :  ∀ {a b} -> Rel (B a b) ℓ) -> Set _
IsPointwiseEquivalence B _∼_ = ∀ a b -> IsEquivalence (_∼_ {a} {b})

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; isEquivalence)
open import Algebra.FunctionProperties using (Op₂; Congruent₂)

_on-≡ : ∀ {ℓa ℓb ℓ} {A : Set ℓa} {B : Rel A ℓb}
        -> (_∼_ :  ∀ {a b} -> Rel (B a b) ℓ)
        -> Rel-on _≡_ B ℓ
_on-≡ _∼_ x y Eq.refl Eq.refl = x ∼ y

instance
  Equiv-on-≡ : ∀ {ℓa ℓb ℓ} {A : Set ℓa} {B : Rel A ℓb} {∼ :  ∀ {a b} -> Rel (B a b) ℓ}
               -> {{_ : IsPointwiseEquivalence B ∼}}
               -> IsEquivalenceOn {{isEquivalence}} B (∼ on-≡)
  Equiv-on-≡ {A = A} {B} {∼} {{ptwise}} = record { refl-on = lem-refl ; sym-on = lem-sym ; trans-on = lem-trans }
    where lem-refl : ∀ {a b} {x : B a b} (p₁ : a ≡ a) (p₂ : b ≡ b)
                     -> (∼ on-≡) x x p₁ p₂
          lem-refl {a} {b} Eq.refl Eq.refl = refl {{ptwise a b}}
          lem-sym : ∀ {a b a' b'} {x : B a b} {y : B a' b'}
                    -> (p₁ : a ≡ a') (p₂ : b ≡ b')
                    -> (∼ on-≡) x y p₁ p₂ -> (∼ on-≡) y x (Eq.sym p₁) (Eq.sym p₂)
          lem-sym {a} {b} Eq.refl Eq.refl = sym {{ptwise a b}}
          lem-trans : ∀ {a b a' b' a'' b''} {x : B a b} {y : B a' b'} {z : B a'' b''}
                      -> (p₁ : a ≡ a') (p₁' : a' ≡ a'') (p₂ : b ≡ b') (p₂' : b' ≡ b'')
                      -> (∼ on-≡) x y p₁ p₂ -> (∼ on-≡) y z p₁' p₂'
                      -> (∼ on-≡) x z (Eq.trans p₁ p₁') (Eq.trans p₂ p₂')
          lem-trans {a} {b} Eq.refl Eq.refl Eq.refl Eq.refl = trans {{ptwise a b}}

cong-on-≡ : ∀ {ℓa ℓb ℓ} {A : Set ℓa} {B : Rel A ℓb} {_∼_ :  ∀ {a b} -> Rel (B a b) ℓ}
            -> {f₁ f₂ : A -> A} (f : ∀ {a b} -> B a b -> B (f₁ a) (f₂ b))
            -> (∀ {a b} {x y : B a b} -> x ∼ y -> f x ∼ f y)
            -> ∀ {a b c d} {x : B a b} {y : B c d}
            -> Heterogenous._≈_ A (_≡_ {A = A}) B (_∼_ on-≡) x y
            -> Heterogenous._≈_ A (_≡_ {A = A}) B (_∼_ on-≡) (f x) (f y)
cong-on-≡ f p (Eq.refl , Eq.refl , eq) = Eq.refl , Eq.refl , p eq

cong₀-on-≡ : ∀ {ℓa ℓb ℓ} {A : Set ℓa} {B : Rel A ℓb} {_∼_ :  ∀ {a b} -> Rel (B a b) ℓ} (e : 2-Op₀ A B)
             -> (∀ (a : A) -> e a ∼ e a)
             -> Heterogenous.Congruent₀-on A (_≡_ {A = A}) B (_∼_ on-≡) e
cong₀-on-≡ _∙_ p a .a Eq.refl = Eq.refl , Eq.refl , p a

cong₂-on-≡ : ∀ {ℓa ℓb ℓ} {A : Set ℓa} {B : Rel A ℓb} {_∼_ :  ∀ {a b} -> Rel (B a b) ℓ} (_∙_ : 2-Op₂ A B)
             -> (∀ {a b c} {x y : B a b} {u v : B b c}
                 -> x ∼ y -> u ∼ v -> (x ∙ u) ∼ (y ∙ v))
             -> Heterogenous.Congruent₂-on A (_≡_ {A = A}) B (_∼_ on-≡) _∙_
cong₂-on-≡ _∙_ p (Eq.refl , Eq.refl , eq1) (Eq.refl , Eq.refl , eq2) = Eq.refl , Eq.refl , p eq1 eq2

instance
  ≡-IsPointwiseEquivalence : ∀ {ℓa ℓb} {A : Set ℓa} {B : Rel A ℓb}
                             -> IsPointwiseEquivalence B (\ {a} {b} -> _≡_ {A = B a b})
  ≡-IsPointwiseEquivalence a b = isEquivalence
