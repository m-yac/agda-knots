
module Data.NVec.Properties {a} {A : Set a} where

open import Data.NVec

open import Data.Nat
import Data.Nat.Properties as ℕProp
open import Data.Product
open import Data.Vec as Vec using (Vec)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; ≡-to-≅; subst; icong)
open import Data.Product.Relation.Pointwise.Dependent as Dep using (Pointwise-≡⇒≡)

open import Algebra
open import Algebra.Structures (_≡_ {A = nVec A})

++-∷-∷ʳ : ∀ (xs : nVec A) (y : A) (ys : nVec A)
           -> xs ++ (y ∷ ys) ≡ (xs ∷ʳ y) ++ ys
++-∷-∷ʳ (m , xs) y (n , ys) = Pointwise-≡⇒≡ (ℕProp.+-suc m n Dep., lem xs y ys)
  where lem : ∀ {m} (xs : Vec A m) (y : A) {n} (ys : Vec A n)
              -> xs Vec.++ (y Vec.∷ ys) ≅ (xs Vec.∷ʳ y) Vec.++ ys
        lem Vec.[] y ys = refl
        lem (x Vec.∷ xs) y ys = icong (Vec _) (ℕProp.+-suc _ _) (x Vec.∷_) (lem xs y ys)

++-assoc : ∀ (xs ys zs : nVec A) -> (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc (k , xs) (m , ys) (n , zs) = Pointwise-≡⇒≡ (ℕProp.+-assoc k m n Dep., lem xs ys zs)
  where lem : ∀ {k} (xs : Vec A k) {m} (ys : Vec A m) {n} (zs : Vec A n)
              -> (xs Vec.++ ys) Vec.++ zs ≅ xs Vec.++ (ys Vec.++ zs)
        lem Vec.[] ys zs = refl
        lem (x Vec.∷ xs) {m} ys {n} zs = icong (Vec _) (ℕProp.+-assoc _ m n) (x Vec.∷_) (lem xs ys zs)

++-identityˡ : ∀ (xs : nVec A) -> [] ++ xs ≡ xs
++-identityˡ _ = refl

++-identityʳ : ∀ (xs : nVec A) -> xs ++ [] ≡ xs
++-identityʳ (n , xs) = Pointwise-≡⇒≡ (ℕProp.+-identityʳ n Dep., lem xs)
  where lem : ∀ {n} (xs : Vec A n) -> xs Vec.++ Vec.[] ≅ xs
        lem Vec.[] = refl
        lem (x Vec.∷ xs) = icong (Vec _) (ℕProp.+-identityʳ _) (x Vec.∷_) (lem xs)

++-isSemigroup : IsSemigroup _++_
++-isSemigroup = record
  { isEquivalence = Eq.isEquivalence
  ; assoc         = ++-assoc
  ; ∙-cong        = Eq.cong₂ _++_ }

++-semigroup : Semigroup _ _
++-semigroup = record { isSemigroup = ++-isSemigroup }

++-[]-isMonoid : IsMonoid _++_ []
++-[]-isMonoid = record
  { isSemigroup = ++-isSemigroup
  ; identity    = ++-identityˡ , ++-identityʳ }

++-[]-monoid : Monoid _ _
++-[]-monoid = record { isMonoid = ++-[]-isMonoid }
