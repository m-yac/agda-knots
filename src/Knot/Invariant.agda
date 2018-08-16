
module Knot.Invariant where

open import Utils
open import Knot.FrontDiagram

open import Data.Bool
open import Data.Integer as ℤ using (ℤ)
open import Data.Nat using (⌊_/2⌋)



half : ℤ -> ℤ
half (ℤ.pos n) = ℤ.pos ⌊ n /2⌋ 
half (ℤ.negsuc n) = ℤ.negsuc ⌊ n /2⌋ 


r×2 : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
r×2 (bGr _ < zero  , _ > x) = ℤ.pred (r×2 x)
r×2 (bGr _ < suc _ , _ > x) = ℤ.suc (r×2 x)
r×2 (cGr _         x) = r×2 x
r×2 (dGr _ < zero  , _ > x) = ℤ.suc (r×2 x)
r×2 (dGr _ < suc _ , _ > x) = ℤ.pred (r×2 x)
r×2 (idPat _)         = ℤ.pos 0

r : ∀ {l} {ls : Vec _ l} -> PatternFD ls -> ℤ
r x = half (r×2 x)


w : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
w (idPat _) = ℤ.pos 0
w (bGr _ _ x) = w x
w (dGr _ _ x) = w x
w {rs = rs} (cGr i x) = cPosty i rs + w x
  where cPosty : ∀ {n} (i : Fin (1 + n)) -> Vec (ℤmod 2) (2 + n) -> ℤ
        cPosty zero (< zero  , _ > ∷ < zero  , _ > ∷ _) = ℤ.pos 1
        cPosty zero (< suc _ , _ > ∷ < suc _ , _ > ∷ _) = ℤ.pos 1
        cPosty zero (_ ∷ _ ∷ _) = ℤ.negsuc 0
        cPosty (suc ()) (_ ∷ _ ∷ [])
        cPosty (suc i) (x ∷ y ∷ z ∷ xs) = cPosty i (y ∷ z ∷ xs)


tb : ∀ {l} {ls : Vec _ l} -> PatternFD ls -> ℤ
tb x = w x + (ℤ.- half (cusps x))
  where cusps : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
        cusps (bGr _ _ x) = ℤ.suc (cusps x)
        cusps (cGr _ x) = cusps x
        cusps (dGr _ _ x) = ℤ.suc (cusps x)
        cusps (idPat _) = ℤ.pos 0
