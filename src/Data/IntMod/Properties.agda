
module Data.IntMod.Properties where

open import Data.IntMod

open import Data.Unit
open import Data.Product as Σ

open import Data.Nat as ℕ using (ℕ; zero; suc; _<_; _>_; _≤_; _≥_)
import Data.Nat.Properties as ℕProp

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤProp

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties

+-assoc : ∀ {n} -> Associative (_≡_ {A = ℤmod n}) _+_
+-assoc {zero} (i , tt) (j , tt) (k , tt) = ≡-on-rep (ℤProp.+-assoc i j k)
+-assoc {suc n} (i , eq₁) (j , eq₂) (k , eq₃) = ≡-on-rep lem
  where lem : Σ.proj₁ (_+_ (_+_ (i , eq₁) (j , eq₂)) (k , eq₃))
              ≡ Σ.proj₁ (_+_ (i , eq₁) (_+_ (j , eq₂) (k , eq₃)))
        lem = begin
          ((i ℕ.+ j) % m     ℕ.+ k      ) % m ≡⟨ %-distribˡ-+ ((i ℕ.+ j) % m) k n ⟩
          ((i ℕ.+ j) % m % m ℕ.+ (k % m)) % m ≡⟨ cong (λ z → (z ℕ.+ k % m) % m) (a%n%n≡a%n (i ℕ.+ j) n) ⟩
          ((i ℕ.+ j) % m     ℕ.+ (k % m)) % m ≡⟨ sym (%-distribˡ-+ (i ℕ.+ j) k n) ⟩
          ((i ℕ.+ j)     ℕ.+ k          ) % m ≡⟨ cong (_% m) (ℕProp.+-assoc i j k) ⟩
          (i       ℕ.+ (j ℕ.+ k)        ) % m ≡⟨ %-distribˡ-+ i (j ℕ.+ k) n ⟩
          ((i % m) ℕ.+ (j ℕ.+ k) % m    ) % m ≡⟨ cong (λ z → ((i % m) ℕ.+ z) % m) (sym (a%n%n≡a%n (j ℕ.+ k) n)) ⟩
          ((i % m) ℕ.+ (j ℕ.+ k) % m % m) % m ≡⟨ sym (%-distribˡ-+ i ((j ℕ.+ k) % m) n) ⟩
          (i       ℕ.+ (j ℕ.+ k) % m    ) % m ∎
          where m = suc n

+-identityˡ : ∀ {n} -> LeftIdentity (_≡_ {A = ℤmod n}) zero-modn _+_
+-identityˡ {zero} (i , tt) = ≡-on-rep (ℤProp.+-identityˡ i)
+-identityˡ {suc n} (i , eq) = ≡-on-rep eq

+-identityʳ : ∀ {n} -> RightIdentity (_≡_ {A = ℤmod n}) zero-modn _+_
+-identityʳ {zero} (i , tt) = ≡-on-rep (ℤProp.+-identityʳ i)
+-identityʳ {suc n} (i , eq) rewrite ℕProp.+-identityʳ i = ≡-on-rep eq

+-identity : ∀ {n} -> Identity (_≡_ {A = ℤmod n}) zero-modn _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : ∀ {n} -> Commutative (_≡_ {A = ℤmod n}) _+_
+-comm {zero} (i , tt) (j , tt) = ≡-on-rep (ℤProp.+-comm i j)
+-comm {suc n} (i , eq₁) (j , eq₂) = ≡-on-rep (cong (_% suc n) (ℕProp.+-comm i j))

+-isSemigroup : ∀ {n} -> IsSemigroup (_≡_ {A = ℤmod n}) _+_
+-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = +-assoc
  ; ∙-cong        = cong₂ _+_ }

+-semigroup : ∀ {n} -> Semigroup _ _
+-semigroup {n} = record { isSemigroup = +-isSemigroup {n} }

+-0-isMonoid : ∀ {n} -> IsMonoid (_≡_ {A = ℤmod n}) _+_ zero-modn
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity }

+-0-monoid : ∀ {n} -> Monoid _ _
+-0-monoid {n} = record { isMonoid = +-0-isMonoid {n} }

+-0-isCommutativeMonoid : ∀ {n} -> IsCommutativeMonoid (_≡_ {A = ℤmod n}) _+_ zero-modn
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ   = +-identityˡ
  ; comm        = +-comm }

+-0-commutativeMonoid : ∀ {n} -> CommutativeMonoid _ _
+-0-commutativeMonoid {n} = record { isCommutativeMonoid = +-0-isCommutativeMonoid {n} }


import Data.Nat.Properties as ℕProp

-- Useful for deriving a contradiction in the (suc n) case when pattern matching on ℤmod (suc n)
[n+a]%n≢a : ∀ n a → (suc n ℕ.+ a) % suc n ≢ (suc n ℕ.+ a)
[n+a]%n≢a n a eq = ℕProp.<⇒≱ lem1 (subst (λ z → z ≥ suc n) (sym eq) lem2)
  where lem1 : ((suc n ℕ.+ a) % suc n) < suc n
        lem1 = a%n<n ((suc n) ℕ.+ a) n
        lem2 : suc n ℕ.+ a ≥ suc n
        lem2 = ℕ.s≤s (ℕProp.≤-stepsʳ a ℕProp.≤-refl)

