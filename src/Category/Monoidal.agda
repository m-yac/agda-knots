
module Category.Monoidal where

open import Relation.Binary.Dependent
open import Algebra.FunctionProperties using (Op₂)
open import Level

open import Algebra using (Monoid)
open import Algebra.Structures using (IsMonoid)
import Category.Monoidal.Structure


record PreMonoidalCategory ℓa ℓb ℓ₁ ℓ₂ : Set (suc (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _∼_
  infix 4 _≈_by_,_
  infixl 7 _∘_
  infixr 7 _∙_
  field
    Obj : Set ℓa
    Hom : Rel Obj ℓb
    _∼_ : Rel Obj ℓ₁
    _≈_by_,_ : Rel-on _∼_ Hom ℓ₂
  open module Structure = Category.Monoidal.Structure _∼_ _≈_by_,_ public
  field
    _∘_ : Op₂ Obj
    id  : Op₀ Obj
    _∙_ : 2-Op₂ Obj Hom
    Id  : 2-Op₀ Obj Hom
    _◅_ : Wskˡ Obj Hom _∘_
    _▻_ : Wskʳ Obj Hom _∘_
    isPreMonoidalCategory : IsPreMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_
    
  open IsPreMonoidalCategory isPreMonoidalCategory public
  
  monoid : Monoid ℓa ℓ₁
  monoid = record { isMonoid = ∘-isMonoid }


record MonoidalCategory ℓa ℓb ℓ₁ ℓ₂ : Set (suc (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _∼_
  infix 4 _≈_by_,_
  infixl 7 _∘_
  infixr 7 _∙_
  field
    Obj : Set ℓa
    Hom : Rel Obj ℓb
    _∼_ : Rel Obj ℓ₁
    _≈_by_,_ : Rel-on _∼_ Hom ℓ₂
  open module Structure = Category.Monoidal.Structure _∼_ _≈_by_,_ public
  field
    _∘_ : Op₂ Obj
    id  : Op₀ Obj
    _∙_ : 2-Op₂ Obj Hom
    Id  : 2-Op₀ Obj Hom
    _◅_ : Wskˡ Obj Hom _∘_
    _▻_ : Wskʳ Obj Hom _∘_
    isMonoidalCategory : IsMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_

  open IsMonoidalCategory isMonoidalCategory public

  preMonoidalCategory : PreMonoidalCategory ℓa ℓb ℓ₁ ℓ₂
  preMonoidalCategory = record { isPreMonoidalCategory = isPreMonoidalCategory }

  open PreMonoidalCategory preMonoidalCategory using (monoid) public


record BraidedMonoidalCategory ℓa ℓb ℓ₁ ℓ₂ : Set (suc (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _∼_
  infix 4 _≈_by_,_
  infixl 7 _∘_
  infixr 7 _∙_
  field
    Obj : Set ℓa
    Hom : Rel Obj ℓb
    _∼_ : Rel Obj ℓ₁
    _≈_by_,_ : Rel-on _∼_ Hom ℓ₂
  open module Structure = Category.Monoidal.Structure _∼_ _≈_by_,_ public
  field
    _∘_ : Op₂ Obj
    id  : Op₀ Obj
    _∙_ : 2-Op₂ Obj Hom
    Id  : 2-Op₀ Obj Hom
    _◅_ : Wskˡ Obj Hom _∘_
    _▻_ : Wskʳ Obj Hom _∘_
    σ   : Braiding Obj Hom _∘_
    σ⁻¹ : Braiding Obj Hom _∘_
    isBraidedMonoidalCategory : IsBraidedMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_ σ σ⁻¹

  open IsBraidedMonoidalCategory isBraidedMonoidalCategory public

  monoidalCategory : MonoidalCategory ℓa ℓb ℓ₁ ℓ₂
  monoidalCategory = record { isMonoidalCategory = isMonoidalCategory }

  open MonoidalCategory monoidalCategory using (monoid; preMonoidalCategory) public


record SymmetricMonoidalCategory ℓa ℓb ℓ₁ ℓ₂ : Set (suc (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _∼_
  infix 4 _≈_by_,_
  infixl 7 _∘_
  infixr 7 _∙_
  field
    Obj : Set ℓa
    Hom : Rel Obj ℓb
    _∼_ : Rel Obj ℓ₁
    _≈_by_,_ : Rel-on _∼_ Hom ℓ₂
  open module Structure = Category.Monoidal.Structure _∼_ _≈_by_,_ public
  field
    _∘_ : Op₂ Obj
    id  : Op₀ Obj
    _∙_ : 2-Op₂ Obj Hom
    Id  : 2-Op₀ Obj Hom
    _◅_ : Wskˡ Obj Hom _∘_
    _▻_ : Wskʳ Obj Hom _∘_
    σ   : Braiding Obj Hom _∘_
    isSymmetricMonoidalCategory : IsSymmetricMonoidalCategory _∘_ id _∙_ Id _◅_ _▻_ σ

  open IsSymmetricMonoidalCategory isSymmetricMonoidalCategory public

  braidedMonoidalCategory : BraidedMonoidalCategory ℓa ℓb ℓ₁ ℓ₂
  braidedMonoidalCategory = record { isBraidedMonoidalCategory = isBraidedMonoidalCategory }

  open BraidedMonoidalCategory braidedMonoidalCategory using (monoid; preMonoidalCategory; monoidalCategory) public
