
module Data.IntMod.Literals where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Unit
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ)
open import Data.Product
open import Data.IntMod

number : ∀ n -> Number (ℤmod n)
number _ .Number.Constraint _ = ⊤
number zero .Number.fromNat m = (ℤ.+ m , tt)
number (suc n) .Number.fromNat m = (m % suc n , a%n%n≡a%n m n)

negative : ∀ n -> Negative (ℤmod n)
negative _ .Negative.Constraint _ = ⊤
negative zero .Negative.fromNeg zero    = (ℤ.pos zero , tt)
negative zero .Negative.fromNeg (suc m) = (ℤ.negsuc m , tt)
negative (suc n) .Negative.fromNeg m = ((suc n ℕ.∸ (m % suc n)) % suc n , a%n%n≡a%n (suc n ℕ.∸ (m % suc n)) n)

