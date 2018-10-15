{-# OPTIONS --rewriting #-}

module Knot.Prelude where

open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public


id : ∀ {a} {A : Set a} -> A -> A
id x = x


open import Relation.Binary using (IsEquivalence) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; subst) public

{-# BUILTIN REWRITE _≡_ #-}

instance
  ≡-IsEquivalence : ∀ {a} {A : Set a} -> IsEquivalence (_≡_ {a} {A})
  ≡-IsEquivalence = Eq.isEquivalence


open import Algebra
open import Algebra.FunctionProperties

module CM = CommutativeMonoid

_+_ : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> Op₂ (CM.Carrier M)
_+_ {{M}} = CM._∙_ M

+-assoc : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> Associative (CM._≈_ M) _+_
+-assoc {{M}} = CM.assoc M

+-cong : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> Congruent₂ (CM._≈_ M) _+_
+-cong {{M}} = CM.∙-cong M

+-identityˡ : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> LeftIdentity (CM._≈_ M) (CM.ε M) _+_
+-identityˡ {{M}} = CM.identityˡ M

+-identityʳ : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> RightIdentity (CM._≈_ M) (CM.ε M) _+_
+-identityʳ {{M}} = CM.identityʳ M

+-comm : ∀ {a ℓ} {{M : CommutativeMonoid a ℓ}} -> Commutative (CM._≈_ M) _+_
+-comm {{M}} = CM.comm M


open import Data.Nat as ℕ using (ℕ; zero; suc) renaming (_⊓_ to max; _⊔_ to min) public
import Data.Nat.Literals as ℕLiterals
import Data.Nat.Properties as ℕProp

instance
  ℕ-Number : Number ℕ
  ℕ-Number = ℕLiterals.number

instance
  ℕ-+-Semigroup : Semigroup _ _
  ℕ-+-Semigroup = ℕProp.+-semigroup

instance
  ℕ-+-Monoid : Monoid _ _
  ℕ-+-Monoid = ℕProp.+-0-monoid

instance
  ℕ-+-CommutativeMonoid : CommutativeMonoid _ _
  ℕ-+-CommutativeMonoid = ℕProp.+-0-commutativeMonoid

-- Now for something unholy... making _+_ definitionally symmetric on its arguments
{-# REWRITE ℕProp.+-identityʳ #-}
{-# REWRITE ℕProp.+-suc #-}
-- ...and, even more unholy, definitionally associative
{-# REWRITE ℕProp.+-assoc #-}


open import Data.Integer as ℤ using (ℤ) public
import Data.Integer.Literals as ℤLiterals
import Data.Integer.Properties as ℤProp

instance
  ℤ-Number : Number ℤ
  ℤ-Number = ℤLiterals.number

instance
  ℤ-Negative : Negative ℤ
  ℤ-Negative = ℤLiterals.negative

instance
  ℤ-+-Semigroup : Semigroup _ _
  ℤ-+-Semigroup = record { isSemigroup = ℤProp.+-isSemigroup }

instance
  ℤ-+-Monoid : Monoid _ _
  ℤ-+-Monoid = record { isMonoid = ℤProp.+-0-isMonoid }

instance
  ℤ-+-CommutativeMonoid : CommutativeMonoid _ _
  ℤ-+-CommutativeMonoid = ℤProp.+-0-commutativeMonoid

instance
  ℤ-+-Group : Group _ _
  ℤ-+-Group = record { isGroup = ℤProp.+-0-isGroup }

instance
  ℤ-+-AbelianGroup : AbelianGroup _ _
  ℤ-+-AbelianGroup = ℤProp.+-0-abelianGroup


open import Data.Fin as Fin using (Fin; zero; suc; pred; Fin′; fromℕ; toℕ) public
import Data.Fin.Literals as FinLiterals

instance
  Fin-Number : ∀ {n} -> Number (Fin n)
  Fin-Number {n} = FinLiterals.number n

at : {n : ℕ} -> Fin n -> Fin (suc n)
at zero = zero
at (suc i) = suc (at i)

at_up_ : {n : ℕ} -> Fin n -> (m : ℕ) -> Fin (m + n)
at_up_ i zero = i
at_up_ i (suc m) = at (at i up m)

neg : ∀ {n} -> Fin n -> Fin n
neg {.suc n} zero = fromℕ n
neg {.suc n} (suc i) = at (neg {n} i)


open import Data.IntMod as ℤmod using (ℤmod; inc; dec; inv-inc-dec; inv-dec-inc) public
import Data.IntMod.Literals as ℤmodLiterals
import Data.IntMod.Properties as ℤmodProp

instance
  ℤmod-Number : ∀ {n} -> Number (ℤmod n)
  ℤmod-Number {n} = ℤmodLiterals.number n

instance
  ℤmod-Negative : ∀ {n} -> Negative (ℤmod n)
  ℤmod-Negative {n} = ℤmodLiterals.negative n

instance
  ℤmod-+-Semigroup : ∀ {n} -> Semigroup _ _
  ℤmod-+-Semigroup {n} = ℤmodProp.+-semigroup {n}

instance
  ℤmod-+-Monoid : ∀ {n} -> Monoid _ _
  ℤmod-+-Monoid {n} = ℤmodProp.+-0-monoid {n}

instance
  ℤmod-+-CommutativeMonoid : ∀ {n} -> CommutativeMonoid _ _
  ℤmod-+-CommutativeMonoid {n} = ℤmodProp.+-0-commutativeMonoid {n}


open import Data.Product as Σ using (Σ-syntax; proj₁; proj₂) public
pattern <_,_> x y = Σ._,_ x y


open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; _++_) public

module VecProp {a} {A : Set a} where

  ++-identityʳ : ∀ {n} (xs : Vec A n) -> xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

  ++-∷ʳ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) (y : A) -> xs ++ (ys ∷ʳ y) ≡ (xs ++ ys) ∷ʳ y
  ++-∷ʳ [] ys y = refl
  ++-∷ʳ (x ∷ xs) ys y = cong (x ∷_) (++-∷ʳ xs ys y)

  ++-assoc : ∀ {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k)
             -> (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  ++-∷-∷ʳ : ∀ {m} (xs : Vec A m) (y : A) {n} (ys : Vec A n) -> xs ++ (y ∷ ys) ≡ (xs ∷ʳ y) ++ ys
  ++-∷-∷ʳ [] y ys = refl
  ++-∷-∷ʳ (x ∷ xs) y ys = cong (x ∷_) (++-∷-∷ʳ xs y ys)

-- Like ℕ, make _++_ compute symmetrically on its arguments
{-# REWRITE VecProp.++-identityʳ #-}
{-# REWRITE VecProp.++-∷ʳ #-}
-- ...and, like ℕ, also associate definitionally
{-# REWRITE VecProp.++-assoc #-}
{-# REWRITE VecProp.++-∷-∷ʳ #-}

insert2 : ∀ {a n} {A : Set a} -> Fin (1 + n) -> A Σ.× A -> Vec A n -> Vec A (2 + n)
insert2 zero < x , y > xs = x ∷ y ∷ xs
insert2 (suc ()) _ []
insert2 (suc i) p (x ∷ xs) = x ∷ insert2 i p xs

swap2 : ∀ {n} {a} {A : Set a} -> Fin (1 + n) -> Vec A (2 + n) -> Vec A (2 + n)
swap2 zero (x ∷ y ∷ xs) = y ∷ x ∷ xs
swap2 {zero} (suc ()) _
swap2 {suc _} (suc i) (x ∷ xs) = x ∷ swap2 i xs

∷ʳ-insert2 : ∀ {a} {A : Set a} {n} (i : Fin (1 + n)) (xs : Vec A n) (p : A Σ.× A) (z : A)
             -> insert2 (at i) p (xs ∷ʳ z) ≡ (insert2 i p xs) ∷ʳ z
∷ʳ-insert2 zero _ _ _ = refl
∷ʳ-insert2 (suc ()) [] _ _
∷ʳ-insert2 (suc i) (x ∷ xs) p z rewrite ∷ʳ-insert2 i xs p z = refl
{-# REWRITE ∷ʳ-insert2 #-} -- for symmetry

∷ʳ-swap2 : ∀ {a} {A : Set a} {n} (i : Fin (1 + n)) (xs : Vec A (2 + n)) (z : A)
             -> swap2 (at i) (xs ∷ʳ z) ≡ (swap2 i xs) ∷ʳ z
∷ʳ-swap2 {n = n} zero (x ∷ y ∷ xs) z = refl
∷ʳ-swap2 {n = zero} (suc ()) xs z
∷ʳ-swap2 {n = suc n} (suc i) (x ∷ xs) z rewrite ∷ʳ-swap2 i xs z = refl
{-# REWRITE ∷ʳ-swap2 #-} -- for symmetry


open import Data.NVec as nVec using (nVec)
  renaming ([] to []*; _∷_,_ to _∷*<_,_>; _∷_ to _∷*_; _++_ to _++*_; _∷ʳ_ to _∷ʳ*_) public
open import Data.NVec.Properties as nVecProp

instance
  nVec-++-Semigroup : ∀ {a} {A : Set a} -> Semigroup _ _
  nVec-++-Semigroup {a} {A} = nVecProp.++-semigroup {a} {A}

instance
  nVec-++-Monoid : ∀ {a} {A : Set a} -> Monoid _ _
  nVec-++-Monoid {a} {A} = nVecProp.++-[]-monoid {a} {A}

