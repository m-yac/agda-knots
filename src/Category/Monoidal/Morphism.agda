
module Category.Monoidal.Morphism where

open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.Dependent
open import Algebra.FunctionProperties using (Op₂)
open import Level

open import Algebra.Morphism as Algebra using (IsMonoidMorphism)
open import Category.Monoidal


module Definitions {ℓa ℓa' ℓb ℓb' ℓ₁ ℓ₂}
                   (A  : Set ℓa ) (B  : Rel A  ℓb )
                   (A' : Set ℓa') (B' : Rel A' ℓb')
                   (_∼_ : Rel A' ℓ₁) (isEquiv : IsEquivalence _∼_)
                   (_≈_by_,_ : Rel-on _∼_ B' ℓ₂) where
   
   open Algebra.Definitions A A' _∼_ public

   Morphism-on : Morphism -> Set _
   Morphism-on φ = ∀ {a b} -> B a b -> B' (φ a) (φ b)


module PreMonoidal {ℓa ℓa' ℓb ℓb' ℓ₁ ℓ₁' ℓ₂ ℓ₂'}
         (M  : PreMonoidalCategory ℓa  ℓb  ℓ₁  ℓ₂ )
         (M' : PreMonoidalCategory ℓa' ℓb' ℓ₁' ℓ₂') where

  private
    module C = PreMonoidalCategory M
    module D = PreMonoidalCategory M'
  open Definitions C.Obj C.Hom D.Obj D.Hom D._∼_ D.isEquivalence D._≈_by_,_ public
  open D using (_∼_; _≈_; refl-on; sym-on; trans-on)
  open IsEquivalence D.isEquivalence

  record IsFunctor (φ : Morphism) (F : Morphism-on φ) : Set (ℓa ⊔ ℓa' ⊔ ℓb ⊔ ℓb' ⊔ ℓ₁ ⊔ ℓ₁' ⊔ ℓ₂ ⊔ ℓ₂') where
    
    field -- equality is preserved
      φ-cong : ∀ {a b} -> a C.∼ b -> (φ a) D.∼ (φ b)
      F-cong : ∀ {a a' b b'} {x : C.Hom a b} {y : C.Hom a' b'}
               -> x C.≈ y -> F x D.≈ F y

    field -- identity elements are preserved
      id-homo : φ C.id ∼ D.id
      Id-homo : ∀ a -> F (C.Id a) ≈ D.Id (φ a)

    field -- composition is perserved
      ∘-homo : ∀ a b -> φ (a C.∘ b) ∼ (φ a) D.∘ (φ b)
      ∙-homo : ∀ {a b c} (x : C.Hom a b) (y : C.Hom b c)
               -> F (x C.∙ y) ≈ (F x) D.∙ (F y)

    field -- whiskering is preserved
      ◅-homo : ∀ {a b c} (x : C.Hom b c) -> F (a C.◅ x) ≈ (φ a) D.◅ (F x)
      ▻-homo : ∀ {a b c} (x : C.Hom a b) -> F (x C.▻ c) ≈ (F x) D.▻ (φ c)

  syntax IsFunctor M M' φ F = M =[ φ , F ]⇒ M'


module Monoidal {ℓa ℓa' ℓb ℓb' ℓ₁ ℓ₁' ℓ₂ ℓ₂'}
                (M  : MonoidalCategory ℓa  ℓb  ℓ₁  ℓ₂ )
                (M' : MonoidalCategory ℓa' ℓb' ℓ₁' ℓ₂') where

  private
    module C = MonoidalCategory M
    module D = MonoidalCategory M'
  open Definitions C.Obj C.Hom D.Obj D.Hom D._∼_ D.isEquivalence D._≈_by_,_ public
  open D using (_∼_; _≈_; refl-on; sym-on; trans-on)
  open IsEquivalence D.isEquivalence

  record IsFunctor (φ : Morphism) (F : Morphism-on φ) : Set (ℓa ⊔ ℓa' ⊔ ℓb ⊔ ℓb' ⊔ ℓ₁ ⊔ ℓ₁' ⊔ ℓ₂ ⊔ ℓ₂') where
    field pm-functor : PreMonoidal.IsFunctor C.preMonoidalCategory D.preMonoidalCategory φ F
    open PreMonoidal.IsFunctor pm-functor public

    ⊗-homo : ∀ {a b c d} (x : C.Hom a b) (y : C.Hom c d) -> F (x C.⊗ y) ≈ (F x) D.⊗ (F y)
    ⊗-homo {a} {b} {c} {d} x y = trans-on (∙-homo (x C.▻ c) (b C.◅ y)) (D.∙-cong (▻-homo x) (◅-homo y))

  syntax IsFunctor M M' φ F = M =[ φ , F ]⇒ M'


module BraidedMonoidal {ℓa ℓa' ℓb ℓb' ℓ₁ ℓ₁' ℓ₂ ℓ₂'}
                       (M  : BraidedMonoidalCategory ℓa  ℓb  ℓ₁  ℓ₂ )
                       (M' : BraidedMonoidalCategory ℓa' ℓb' ℓ₁' ℓ₂') where

  private
    module C = BraidedMonoidalCategory M
    module D = BraidedMonoidalCategory M'
  open Definitions C.Obj C.Hom D.Obj D.Hom D._∼_ D.isEquivalence D._≈_by_,_ public
  open D using (_∼_; _≈_; refl-on; sym-on; trans-on)
  open IsEquivalence D.isEquivalence

  record IsFunctor (φ : Morphism) (F : Morphism-on φ) : Set (ℓa ⊔ ℓa' ⊔ ℓb ⊔ ℓb' ⊔ ℓ₁ ⊔ ℓ₁' ⊔ ℓ₂ ⊔ ℓ₂') where
    field m-functor : Monoidal.IsFunctor C.monoidalCategory D.monoidalCategory φ F
    open Monoidal.IsFunctor m-functor public
    
    field
      σ-homo : ∀ a b -> F (C.σ a b) ≈ D.σ (φ a) (φ b)

  syntax IsFunctor M M' φ F = M =[ φ , F ]⇒ M'



module SymmetricMonoidal {ℓa ℓa' ℓb ℓb' ℓ₁ ℓ₁' ℓ₂ ℓ₂'}
         (M  : SymmetricMonoidalCategory ℓa  ℓb  ℓ₁  ℓ₂ )
         (M' : SymmetricMonoidalCategory ℓa' ℓb' ℓ₁' ℓ₂') where

  private
    module C = SymmetricMonoidalCategory M
    module D = SymmetricMonoidalCategory M'
  open Definitions C.Obj C.Hom D.Obj D.Hom D._∼_ D.isEquivalence D._≈_by_,_ public
  open D using (_∼_; _≈_; refl-on; sym-on; trans-on) public
  open IsEquivalence D.isEquivalence

  record IsFunctor (φ : Morphism) (F : Morphism-on φ) : Set (ℓa ⊔ ℓa' ⊔ ℓb ⊔ ℓb' ⊔ ℓ₁ ⊔ ℓ₁' ⊔ ℓ₂ ⊔ ℓ₂') where
    field bm-functor : BraidedMonoidal.IsFunctor C.braidedMonoidalCategory D.braidedMonoidalCategory φ F
    open BraidedMonoidal.IsFunctor bm-functor public

  syntax IsFunctor M M' φ F = M =[ φ , F ]⇒ M'
