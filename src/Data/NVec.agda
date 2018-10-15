
module Data.NVec where

open import Data.Nat
import Data.Nat.Properties as ℕProp
open import Data.Product
open import Data.Vec as Vec using (Vec)

nVec : ∀ {a} -> Set a -> Set a
nVec A = Σ[ n ∈ ℕ ] Vec A n

pattern [] = zero , Vec.[]
pattern  _∷_,_ x n xs = suc n , x Vec.∷ xs

_∷_ : ∀ {a} {A : Set a} -> A -> nVec A -> nVec A
_∷_ x (n , xs) = suc n , x Vec.∷ xs
infixr 5 _∷_

_++_ : ∀ {a} {A : Set a} -> nVec A -> nVec A -> nVec A
_++_ (n , xs) (m , ys) = n + m , xs Vec.++ ys
infixr 5 _++_

_∷ʳ_ : ∀ {a} {A : Set a} -> nVec A -> A -> nVec A
_∷ʳ_ (n , xs) x = suc n , xs Vec.∷ʳ x
infixl 5 _∷ʳ_
