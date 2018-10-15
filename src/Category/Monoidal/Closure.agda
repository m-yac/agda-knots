
open import Relation.Binary using (Rel; Symmetric)
open import Relation.Binary.Dependent
open import Level using (_⊔_)
open import Category.Monoidal

module Category.Monoidal.Closure {ℓa ℓb ℓ₁ ℓ₂}
                                 {{M : PreMonoidalCategory ℓa ℓb ℓ₁ ℓ₂}} where
open PreMonoidalCategory M


-- The monoidal closure of a relation
module _ {ℓ} (R : ∀ {a b} -> Rel (Hom a b) ℓ) where

  data MonoidalClosure : ∀ {a b} -> Rel (Hom a b) (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ) where
    emb : ∀ {x y} {X Y : Hom x y} -> R X Y
          -> ∀ (a b : Obj)
          -> ∀ {l} (L : Hom l (a ∘ (x ∘ b))  )
               {r} (R : Hom   (a ∘ (y ∘ b)) r)
          -> MonoidalClosure (L ∙ (a ◅ (X ▻ b)) ∙ R) (L ∙ (a ◅ (Y ▻ b)) ∙ R)

symM : ∀ {ℓ} {R : ∀ {a b} -> Rel (Hom a b) ℓ}
       -> (∀ {a b} -> Symmetric (R {a} {b}))
       ->  ∀ {a b} -> Symmetric (MonoidalClosure R {a} {b})
symM sym (emb p a b L R) = emb (sym p) a b L R


-- The monoidal closure of a dependent relation
module _ {ℓ} (R : Rel-on _∼_ Hom ℓ) where

  open Heterogenous Obj _∼_ Hom R renaming (_≈_ to _≈R_)
  open import Data.Product using (proj₁; proj₂)

  data MonoidalClosure-on : Rel-on _∼_ Hom (ℓa ⊔ ℓb ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ) where
    emb-on : ∀ {x x' y y'} {X : Hom x y} {Y : Hom x' y'} (P : X ≈R Y)
             -> ∀ (a b : Obj)
             -> ∀ {l l'} (L : Hom l (a ∘ (x ∘ b))  ) (pl : l ∼ l')
                  {r r'} (R : Hom   (a ∘ (y ∘ b)) r) (pr : r ∼ r')
             -> let L' : Hom l' (a ∘ (x' ∘ b))
                    L' = B-cong pl (∘-cong refl (∘-cong        (proj₁ P)  refl))    L
                    R' : Hom   (a ∘ (y' ∘ b)) r'
                    R' = B-cong    (∘-cong refl (∘-cong (proj₁ (proj₂ P)) refl)) pr R
                in MonoidalClosure-on (L ∙ (a ◅ (X ▻ b)) ∙ R) (L' ∙ (a ◅ (Y ▻ b)) ∙ R') pl pr
