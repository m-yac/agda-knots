
module Category.Monoidal.Instances where

open import Category.Monoidal
open import Category.Monoidal.Structure

open import Algebra
open import Algebra.Structures
open import Relation.Binary.Dependent
open import Algebra.FunctionProperties using (Op₂)
open import Function using (id)
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)


-- ⊤ is the trivial monoid

instance
  ⊤-isMonoid : IsMonoid (_≡_ {A = ⊤}) (\ _ _ -> tt) tt
  ⊤-isMonoid = record { isSemigroup = record
                          { isEquivalence = Eq.isEquivalence
                          ; ∙-cong = λ _ _ → Eq.refl
                          ; assoc = λ _ _ _ → Eq.refl }
                      ; identity = (λ _ → Eq.refl) , (λ _ → Eq.refl) }



-- Every monoid is a (premonoidal) category on ⊤

IsMonoid-IsPreMonoidalCategory
  : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {_∙_ : Op₂ A} {id : Op₀ A}
    -> IsMonoid _∼_ _∙_ id
    -> IsPreMonoidalCategory (_≡_ {A = ⊤}) (_∼_ on-≡)
                             (\ _ _ -> tt) tt _∙_ (\ _ -> id)
                             (\ _ x -> x) (\ x _ -> x)
IsMonoid-IsPreMonoidalCategory {A = A} {_∼_} {_∙_} isMonoid = record
  { ∘-isMonoid = ⊤-isMonoid
  -- axioms of a monoid ~> axioms of a category
  ; isEquivOn = Equiv-on-≡ {{\ _ _ -> isEquivalence}}
  ; ∙-cong = cong₂-on-≡ _∙_ ∙-cong
  ; 2-assoc = λ x y z -> wrap (assoc x y z)
  ; 2-identityˡ = λ x → wrap (identityˡ x)
  ; 2-identityʳ = λ x → wrap (identityʳ x)
  -- the rest are trivial
  ; wsk-congˡ = λ _ → id
  ; wsk-congʳ = λ _ → id
  ; wsk-assoc = λ _ → refl-on
  ; wsk-identityˡ = λ _ → refl-on
  ; wsk-identityʳ = λ _ → refl-on
  ; ∘-acts-on-wskˡ = λ _ → refl-on
  ; ∘-acts-on-wskʳ = λ _ → refl-on
  ; wsk-2-identityˡ = refl-on
  ; wsk-2-identityʳ = refl-on
  ; wsk-distribˡ = λ _ _ → refl-on
  ; wsk-distribʳ = λ _ _ → refl-on }
  where open IsMonoid isMonoid
        open Heterogenous ⊤ _≡_ (\ _ _ -> A) (_∼_ on-≡)
        open HeterogenousEquivalenceOn {{_}} {{Equiv-on-≡ {{\ _ _ -> isEquivalence}}}}

instance
  Monoid-PreMonoidalCategory : ∀ {a ℓ} {{_ : Monoid a ℓ}} -> PreMonoidalCategory _ a _ ℓ
  Monoid-PreMonoidalCategory {{record { isMonoid = isMonoid }}}
    = record { isPreMonoidalCategory = IsMonoid-IsPreMonoidalCategory isMonoid }



-- Every commutative monoid is a symmetric monoidal category on ⊤

IsCommutativeMonoid-IsMonoidalCategory
  : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {_∙_ : Op₂ A} {id : Op₀ A}
    -> IsCommutativeMonoid _∼_ _∙_ id
    -> IsMonoidalCategory (_≡_ {A = ⊤}) (_∼_ on-≡)
                          (\ _ _ -> tt) tt _∙_ (\ _ -> id)
                          (\ _ x -> x) (\ x _ -> x)
IsCommutativeMonoid-IsMonoidalCategory {A = A} {_∼_} isCommutativeMonoid = record
  { isPreMonoidalCategory = IsMonoid-IsPreMonoidalCategory isMonoid
  -- lifting commutativity
  ; inter = λ x y → wrap (comm x y) }
  where open IsCommutativeMonoid isCommutativeMonoid
        open Heterogenous ⊤ _≡_ (\ _ _ -> A) (_∼_ on-≡)

IsCommutativeMonoid-IsSymmetricMonoidalCategory
  : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {_∙_ : Op₂ A} {id : Op₀ A}
    -> IsCommutativeMonoid _∼_ _∙_ id
    -> IsSymmetricMonoidalCategory (_≡_ {A = ⊤}) (_∼_ on-≡)
                                   (\ _ _ -> tt) tt _∙_ (\ _ -> id)
                                   (\ _ x -> x) (\ x _ -> x) (\ _ _ -> id)
IsCommutativeMonoid-IsSymmetricMonoidalCategory {A = A} {_∼_} {_∙_} {id} isCommutativeMonoid = record
  { isMonoidalCategory = IsCommutativeMonoid-IsMonoidalCategory isCommutativeMonoid
  -- these follow directly from monoid laws and commutativity
  ; σ-cong = λ _ _ -> refl-on
  ; σ-nat = λ x y → wrap (trans (identityʳ (x ∙ y)) (trans (comm x y) (sym (identityˡ (y ∙ x)))))
  ; σ-inv = λ _ _ → wrap (identityˡ id) }
  where open IsCommutativeMonoid isCommutativeMonoid
        open Heterogenous ⊤ _≡_ (\ _ _ -> A) (_∼_ on-≡)
        open HeterogenousEquivalenceOn {{_}} {{Equiv-on-≡ {{\ _ _ -> isEquivalence}}}}

-- we get this for free from IsSymmetricMonoidalCategory
IsCommutativeMonoid-IsBraidedMonoidalCategory
  : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {_∙_ : Op₂ A} {id : Op₀ A}
    -> IsCommutativeMonoid _∼_ _∙_ id
    -> IsBraidedMonoidalCategory (_≡_ {A = ⊤}) (_∼_ on-≡)
                                 (\ _ _ -> tt) tt _∙_ (\ _ -> id)
                                 (\ _ x -> x) (\ x _ -> x) (\ _ _ -> id) (\ _ _ -> id)
IsCommutativeMonoid-IsBraidedMonoidalCategory isCommutativeMonoid
  = IsSymmetricMonoidalCategory.isBraidedMonoidalCategory
      (IsCommutativeMonoid-IsSymmetricMonoidalCategory isCommutativeMonoid)

instance
  CommutativeMonoid-MonoidalCategory : ∀ {a ℓ} {{_ : CommutativeMonoid a ℓ}} -> MonoidalCategory _ a _ ℓ
  CommutativeMonoid-MonoidalCategory {{record { isCommutativeMonoid = isCommutativeMonoid }}}
    = record { isMonoidalCategory = IsCommutativeMonoid-IsMonoidalCategory isCommutativeMonoid }

instance
  CommutativeMonoid-SymmetricMonoidalCategory : ∀ {a ℓ} {{_ : CommutativeMonoid a ℓ}} -> SymmetricMonoidalCategory _ a _ ℓ
  CommutativeMonoid-SymmetricMonoidalCategory {{record { isCommutativeMonoid = isCommutativeMonoid }}}
    = record { isSymmetricMonoidalCategory = IsCommutativeMonoid-IsSymmetricMonoidalCategory isCommutativeMonoid }

instance
  CommutativeMonoid-BraidedMonoidalCategory : ∀ {a ℓ} {{_ : CommutativeMonoid a ℓ}} -> BraidedMonoidalCategory _ a _ ℓ
  CommutativeMonoid-BraidedMonoidalCategory {{record { isCommutativeMonoid = isCommutativeMonoid }}}
    = record { isBraidedMonoidalCategory = IsCommutativeMonoid-IsBraidedMonoidalCategory isCommutativeMonoid }
