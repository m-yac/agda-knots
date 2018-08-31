
open import Relation.Binary.Dependent
open import Level using (_⊔_)

module Category.Monoidal.Structure {ℓa ℓb ℓ₁ ℓ₂} {A : Set ℓa} {B : Rel A ℓb}
                                   (_∼_ : Rel A ℓ₁) (_≈_by_,_ : Rel-on _∼_ B ℓ₂) where

open import Algebra.FunctionProperties using (Op₂)
open import Algebra.Structures as Algebra using (IsMonoid)


Wskˡ : ∀ (A : Set ℓa) (B : Rel A ℓb) -> Op₂ A -> Set (ℓa ⊔ ℓb)
Wskˡ A B _∘_ = (a : A) -> ∀ {b c} -> B b c -> B (a ∘ b) (a ∘ c)

Wskʳ : ∀ (A : Set ℓa) (B : Rel A ℓb) -> Op₂ A -> Set (ℓa ⊔ ℓb)
Wskʳ A B _∘_ = ∀ {a b} -> B a b -> (c : A) -> B (a ∘ c) (b ∘ c)

Braiding : ∀ (A : Set ℓa) (B : Rel A ℓb) -> Op₂ A -> Set (ℓa ⊔ ℓb)
Braiding A B _∘_ = ∀ a b -> B (a ∘ b) (b ∘ a)


-- A (strict) monoidal category (AKA a 2-category with one object) missing the interchange law
-- See: https://ncatlab.org/nlab/show/strict+2-category
-- Note: *All* infix notations reversed with respect to the standard
record IsPreMonoidalCategory (_∘_ : Op₂ A) (id : Op₀ A) (_∙_ : 2-Op₂ A B) (Id : 2-Op₀ A B)
                             (_◅_ : Wskˡ A B _∘_) (_▻_ : Wskʳ A B _∘_) : Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂) where
       
       field -- _∘_ forms a monoid
         ∘-isMonoid    : IsMonoid _∼_ _∘_ id

       open IsMonoid ∘-isMonoid renaming (∙-cong to ∘-cong) public

       open Heterogenous A _∼_ B _≈_by_,_ public

       field -- _∙_ forms a category
         isEquivOn   : IsEquivalenceOn {{isEquivalence}} B _≈_by_,_
         ∙-cong      : Congruent₂-on _∙_
         2-assoc     : ∀ {a b c d} (x : B a b) (y : B b c) (z : B c d)
                       -> ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
         2-identityˡ : ∀ {a b} (x : B a b) -> (Id a ∙ x) ≈ x
         2-identityʳ : ∀ {a b} (x : B a b) -> (x ∙ Id b) ≈ x

       field -- whiskering is well defined
         wsk-congˡ : ∀ {a a' b b' c c'} {x : B b c} {y : B b' c'}
                     -> a ∼ a' -> x ≈ y -> a ◅ x ≈ a' ◅ y
         wsk-congʳ : ∀ {a a' b b' c c'} {x : B a b} {y : B a' b'}
                     -> c ∼ c' -> x ≈ y -> x ▻ c ≈ y ▻ c'

       field -- whiskering is associative
         wsk-assoc : ∀ {a b c d} (x : B b c)
                     -> ((a ◅ x) ▻ d) ≈ (a ◅ (x ▻ d)) -- by assoc a b d , assoc a c d

       field -- whiskering is a monoid action on _∘_
         wsk-identityˡ  : ∀ {a b} (x : B a b) -> (id ◅ x) ≈ x -- by identityˡ a , identityˡ b
         wsk-identityʳ  : ∀ {a b} (x : B a b) -> (x ▻ id) ≈ x -- by identityʳ a , identityʳ b 
         ∘-acts-on-wskˡ : ∀ {a b c d} (x : B c d)
                          -> ((a ∘ b) ◅ x) ≈ (a ◅ (b ◅ x)) -- by assoc a b c , assoc a b d
         ∘-acts-on-wskʳ : ∀ {a b c d} (x : B a b)
                          -> ((x ▻ c) ▻ d) ≈ (x ▻ (c ∘ d)) -- by assoc a c d , assoc b c d

       field -- whiskering is an endofunctor on _∙_
         wsk-2-identityˡ : ∀ {a b} -> (a ◅ Id b) ≈ (Id (a ∘ b))
         wsk-2-identityʳ : ∀ {a b} -> (Id a ▻ b) ≈ (Id (a ∘ b))
         wsk-distribˡ    : ∀ {a b c d} (x : B b c) (y : B c d)
                           -> (a ◅ (x ∙ y)) ≈ ((a ◅ x) ∙ (a ◅ y))
         wsk-distribʳ    : ∀ {a b c d} (x : B a b) (y : B b c)
                           -> ((x ∙ y) ▻ d) ≈ ((x ▻ d) ∙ (y ▻ d))

       open HeterogenousEquivalenceOn {{isEquivalence}} {{isEquivOn}} public


-- A (strict) monoidal category, defined in terms of a premonoidal category
record IsMonoidalCategory (_∘_ : Op₂ A) (id : Op₀ A) (_∙_ : 2-Op₂ A B) (Id : 2-Op₀ A B)
                          (_◅_ : Wskˡ A B _∘_) (_▻_ : Wskʳ A B _∘_) : Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂) where

       field isPreMonoidalCategory : IsPreMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_
       open IsPreMonoidalCategory isPreMonoidalCategory public
 
       field -- interchange law
         inter : ∀ {a b c d} (x : B a b) (y : B c d)
                 -> ((x ▻ c) ∙ (b ◅ y)) ≈ ((a ◅ y) ∙ (x ▻ d))

       -- one of the two equivalent ways to define horizontal composition
       infix 8 _⊗_
       _⊗_ : ∀ {a b c d} -> B a b -> B c d -> B (a ∘ c) (b ∘ d)
       _⊗_ {a} {b} {c} {d} x y = (x ▻ c) ∙ (b ◅ y)


-- A (strict) braided monoidal category
record IsBraidedMonoidalCategory (_∘_ : Op₂ A) (id : Op₀ A) (_∙_ : 2-Op₂ A B) (Id : 2-Op₀ A B)
                                 (_◅_ : Wskˡ A B _∘_) (_▻_ : Wskʳ A B _∘_)
                                 (σ σ⁻¹ : Braiding A B _∘_) : Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂) where

       field isMonoidalCategory : IsMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_
       open IsMonoidalCategory isMonoidalCategory public

       field -- σ and σ⁻¹ are well-defined
         σ-cong   : ∀ {a a' b b'} -> a ∼ a' -> b ∼ b' -> σ a b ≈ σ a' b'
         σ⁻¹-cong : ∀ {a a' b b'} -> a ∼ a' -> b ∼ b' -> σ⁻¹ a b ≈ σ⁻¹ a' b'

       field -- σ is a natural isomorphism with inverse σ⁻¹
         σ-nat  : ∀ {a b c d : A} (x : B a b) (y : B c d)
                  -> ((x ⊗ y) ∙ σ b d) ≈ (σ a c ∙ (y ⊗ x))
         σ-invˡ : ∀ (a b : A) -> (σ a b ∙ σ⁻¹ b a) ≈ Id (a ∘ b)
         σ-invʳ : ∀ (a b : A) -> (σ⁻¹ b a ∙ σ a b) ≈ Id (b ∘ a)

       -- σ⁻¹ is also a natural transformation
       σ⁻¹-nat : ∀ {a b c d : A} (y : B c d) (x : B a b)
                 -> ((y ⊗ x) ∙ σ⁻¹ d b) ≈ (σ⁻¹ c a ∙ (x ⊗ y))
       σ⁻¹-nat {a} {b} {c} {d} y x = sym-on lem4
         where -- starting with σ-nat, right-compose with σ⁻¹ d b
               lem1 : (((x ⊗ y) ∙ σ b d) ∙ σ⁻¹ d b) ≈ ((σ a c ∙ (y ⊗ x)) ∙ σ⁻¹ d b)
               lem1 = ∙-cong (σ-nat x y) refl-on
               -- simplify the left hand side
               lem2 : (x ⊗ y) ≈ ((σ a c ∙ (y ⊗ x)) ∙ σ⁻¹ d b)
               lem2 =  trans-on (sym-on (2-identityʳ (x ⊗ y)))
                      (trans-on (sym-on (∙-cong refl-on (σ-invˡ b d)))
                      (trans-on (sym-on (2-assoc (x ⊗ y) (σ b d) (σ⁻¹ d b)))
                                lem1))
               -- left-compose with σ⁻¹ c a
               lem3 : (σ⁻¹ c a ∙ (x ⊗ y)) ≈ (σ⁻¹ c a ∙ (σ a c ∙ ((y ⊗ x) ∙ σ⁻¹ d b)))
               lem3 = ∙-cong refl-on (trans-on lem2 (2-assoc (σ a c) (y ⊗ x) (σ⁻¹ d b)))
               -- simplify the right hand side
               lem4 : (σ⁻¹ c a ∙ (x ⊗ y)) ≈ ((y ⊗ x) ∙ σ⁻¹ d b)
               lem4 =  trans-on lem3
                      (trans-on (sym-on (2-assoc (σ⁻¹ c a) (σ a c) ((y ⊗ x) ∙ σ⁻¹ d b)))
                      (trans-on (∙-cong (σ-invʳ a c) refl-on)
                                (2-identityˡ ((y ⊗ x) ∙ σ⁻¹ d b))))


-- A (strict) symmetric monoidal category
record IsSymmetricMonoidalCategory (_∘_ : Op₂ A) (id : Op₀ A) (_∙_ : 2-Op₂ A B) (Id : 2-Op₀ A B)
                                   (_◅_ : Wskˡ A B _∘_) (_▻_ : Wskʳ A B _∘_)
                                   (σ : Braiding A B _∘_) : Set (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂) where

       field isMonoidalCategory : IsMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_
       open IsMonoidalCategory isMonoidalCategory public

       field -- σ is well-defined
         σ-cong : ∀ {a a' b b'} -> a ∼ a' -> b ∼ b' -> σ a b ≈ σ a' b'

       field -- σ is a self-inverse natural isomorphism
         σ-nat : ∀ {a b c d : A} (x : B a b) (y : B c d)
                 -> ((x ⊗ y) ∙ σ b d) ≈ (σ a c ∙ (y ⊗ x))
         σ-inv : ∀ (a b : A) -> (σ a b ∙ σ b a) ≈ Id (a ∘ b)

       isBraidedMonoidalCategory : IsBraidedMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_ σ σ
       isBraidedMonoidalCategory
         = record { isMonoidalCategory = isMonoidalCategory
                  ; σ-cong = σ-cong ; σ⁻¹-cong = σ-cong ; σ-nat = σ-nat ; σ-invˡ = σ-inv
                  ; σ-invʳ = λ a b → σ-inv b a }
