
module FrontDiagrams where

open import Utils

open import Data.Nat.Properties
open import Data.Fin as F using (Fin; zero; suc; Fin′; #_; fromℕ; fromℕ≤; toℕ; inject; inject!; inject+; raise)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Data.Nat.Show



data LegFD : ℕ -> ℕ -> Set where
  bCons : {m n : ℕ} (i : Fin (1 + n)) -> LegFD m n       -> LegFD m (2 + n)
  cCons : {m n : ℕ} (i : Fin (1 + n)) -> LegFD m (2 + n) -> LegFD m (2 + n)
  dCons : {m n : ℕ} (i : Fin (1 + n)) -> LegFD m (2 + n) -> LegFD m n
  idPat : (n : ℕ) -> LegFD n n

LegLinkFD    =       LegFD 0 0
LegPatternFD = \ n → LegFD n n


b_ : {m n : ℕ} (i : ℕ) {ineq : True (suc i ≤? suc n)} -> LegFD m n -> LegFD m (2 + n)
b_ _ {ineq} = bCons (fromℕ≤ (toWitness ineq))

c_ : {m n : ℕ} (i : ℕ) {ineq : True (suc i ≤? suc n)} -> LegFD m (2 + n) -> LegFD m (2 + n)
c_ _ {ineq} = cCons (fromℕ≤ (toWitness ineq))

d_ : {m n : ℕ} (i : ℕ) {ineq : True (suc i ≤? suc n)} -> LegFD m (2 + n) -> LegFD m n
d_ _ {ineq} = dCons (fromℕ≤ (toWitness ineq))

_,_ : {m n m' n' : ℕ} -> LegFD m n -> (LegFD m n -> LegFD m' n') -> LegFD m' n'
Λ , f = f Λ
infixl 5 _,_

_<:_ : {m' n' : ℕ} -> (n : ℕ) -> (LegFD n n -> LegFD m' n') -> LegFD m' n'
n <: f = f (idPat n)
infixl 5 _<:_

cons : {m n k : ℕ} -> LegFD m n -> LegFD n k -> LegFD m k
cons x (bCons i y) = (cons x y) , bCons i
cons x (cCons i y) = (cons x y) , cCons i
cons x (dCons i y) = (cons x y) , dCons i
cons x (idPat n) = x

instance
  LegFD-Dep+ : HasDependent+ ℕ LegFD
  LegFD-Dep+ = record { _+_ = cons; unit = idPat }


ppr : {m n : ℕ} -> LegFD m n -> String
ppr (bCons i x) = (ppr x) ++ "b" ++ (Data.Nat.Show.show (toℕ i)) ++ " "
ppr (cCons i x) = (ppr x) ++ "c" ++ (Data.Nat.Show.show (toℕ i)) ++ " "
ppr (dCons i x) = (ppr x) ++ "d" ++ (Data.Nat.Show.show (toℕ i)) ++ " "
ppr (idPat n) = ""


ex-3-1 : LegLinkFD
ex-3-1 = 0 <: b 0 , c 0 , d 0

ex-m-3-1 : LegLinkFD
ex-m-3-1 = 0 <: b 0 , b 1 , b 3 , c 0 , c 2 , c 4 , d 3 , d 1 , d 0

WH : LegPatternFD 2
WH = 2 <: b 1 , c 0 , c 2 , d 1



addStrandsBelow : {m n : ℕ} (k : ℕ) -> LegFD m n -> LegFD (m + k) (n + k)
addStrandsBelow k (bCons {m} {n} i x) = bCons (inject+ k i) (addStrandsBelow k x)
addStrandsBelow k (cCons {m} {n} i x) = cCons (inject+ k i) (addStrandsBelow k x)
addStrandsBelow k (dCons {m} {n} i x) = dCons (inject+ k i) (addStrandsBelow k x)
addStrandsBelow k (idPat n)           = idPat (n + k)

addStrandsBelow' : {m n : ℕ} (k : ℕ) -> LegFD m n -> LegFD (k + m) (k + n)
addStrandsBelow' {m} {n} k x rewrite +-comm k m | +-comm k n = addStrandsBelow k x


raise' : ∀ {m} n → Fin m → Fin (m + n)
raise' {m} n i rewrite +-comm m n = raise n i

addStrandsAbove : {m n : ℕ} (k : ℕ) -> LegFD m n -> LegFD (m + k) (n + k)
addStrandsAbove k (bCons {m} {n} i x) = bCons (raise' k i) (addStrandsAbove k x)
addStrandsAbove k (cCons {m} {n} i x) = cCons (raise' k i) (addStrandsAbove k x)
addStrandsAbove k (dCons {m} {n} i x) = dCons (raise' k i) (addStrandsAbove k x)
addStrandsAbove k (idPat n) = idPat (n + k)

addStrandsAbove' : {m n : ℕ} (k : ℕ) -> LegFD m n -> LegFD (k + m) (k + n)
addStrandsAbove' {m} {n} k x rewrite +-comm k m | +-comm k n = addStrandsAbove k x




htw : (n : ℕ) -> LegPatternFD n
htw (suc (suc n)) = bsig (suc (suc n)) + addStrandsBelow' 1 (htw (suc n))
  where bsig : (n : ℕ) -> LegPatternFD n
        bsig (suc (suc n)) = addStrandsBelow' 1 (bsig (suc n)) , cCons (fromℕ n)
        bsig n             = idPat n
htw n             = idPat n

tw : (n : ℕ) -> LegPatternFD n
tw n = 2 × htw n


