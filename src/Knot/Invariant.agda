
module Knot.Invariant where

open import Utils
open import Knot.FrontDiagram
open import Knot.Isotopy

open import Data.Bool
open import Data.Integer as ℤ using (ℤ)
open import Data.Nat using (⌊_/2⌋)

half : ℤ -> ℤ
half (ℤ.pos n) = ℤ.pos ⌊ n /2⌋ 
half (ℤ.negsuc n) = ℤ.negsuc ⌊ n /2⌋

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using ()

instance
  _≡_-Equivalence : ∀ {a} {A : Set a} -> IsEquivalence (_≡_ {a} {A})
  _≡_-Equivalence = Eq.isEquivalence

import Data.Integer.Properties as ℤProp
open import Function using (_∘_; _on_)



r×2 : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
r×2 (bGr _ < zero  , _ > x) = -1 + r×2 x
r×2 (bGr _ < suc _ , _ > x) =  1 + r×2 x
r×2 (cGr _               x) =      r×2 x
r×2 (dGr _ < zero  , _ > x) =  1 + r×2 x
r×2 (dGr _ < suc _ , _ > x) = -1 + r×2 x
r×2 (idPat _)               =  0

r : ∀ {l} {ls : Vec _ l} -> PatternFD ls -> ℤ
r x = half (r×2 x)

r×2-invar : Legn Invariant r×2 wrt _≡_
r×2-invar = pv-invariant r×2 (by-split-+ sp+ rp+) (by-split-∷* sp∷* rp∷*) gen-inv

  where sp+ : (\ (x y : ℤ) -> y + x) splits-+-on r×2
        sp+ Λl (bGr i < zero  , _ > Λr) rewrite ℤProp.+-assoc -1 (r×2 Λr) (r×2 Λl) = cong (λ z → -1 + z) (sp+ Λl Λr)
        sp+ Λl (bGr i < suc _ , _ > Λr) rewrite ℤProp.+-assoc  1 (r×2 Λr) (r×2 Λl) = cong (λ z →  1 + z) (sp+ Λl Λr)
        sp+ Λl (cGr i Λr) = sp+ Λl Λr
        sp+ Λl (dGr i < zero  , _ > Λr) rewrite ℤProp.+-assoc  1 (r×2 Λr) (r×2 Λl) = cong (λ z →  1 + z) (sp+ Λl Λr)
        sp+ Λl (dGr i < suc _ , _ > Λr) rewrite ℤProp.+-assoc -1 (r×2 Λr) (r×2 Λl) = cong (λ z → -1 + z) (sp+ Λl Λr)
        sp+ Λl (idPat ls) rewrite ℤProp.+-identityˡ (r×2 Λl) = refl

        rp+ : (\ (x y : ℤ) -> y + x) resp-+-wrt _≡_
        rp+ a b refl refl = refl
        
        sp∷* : (\ _ (y : ℤ) -> y) splits-∷*-on r×2
        sp∷* μ (bGr i < zero  , _ > Λ) = cong (λ z → -1 + z) (sp∷* μ Λ)
        sp∷* μ (bGr i < suc _ , _ > Λ) = cong (λ z →  1 + z) (sp∷* μ Λ)
        sp∷* μ (cGr i Λ) = sp∷* μ Λ
        sp∷* μ (dGr i < zero  , _ > Λ) = cong (λ z →  1 + z) (sp∷* μ Λ)
        sp∷* μ (dGr i < suc _ , _ > Λ) = cong (λ z → -1 + z) (sp∷* μ Λ)
        sp∷* μ (idPat ls) = refl

        rp∷* : (\ _ (y : ℤ) -> y) resp-∷*-wrt _≡_
        rp∷* xs b refl = refl

        gen-inv : Legn Gen-Invariant r×2 wrt _≡_
        gen-inv (R1-a {μ = < zero  , _ >}) = refl
        gen-inv (R1-a {μ = < suc _ , _ >}) = refl
        gen-inv (R1-b {μ = < zero  , _ >}) = refl
        gen-inv (R1-b {μ = < suc _ , _ >}) = refl
        gen-inv (R2-b-a {μ = < zero  , _ >}) = refl
        gen-inv (R2-b-a {μ = < suc _ , _ >}) = refl
        gen-inv (R2-b-b {μ = < zero  , _ >}) = refl
        gen-inv (R2-b-b {μ = < suc _ , _ >}) = refl
        gen-inv (R2-d-a {μ = < zero  , _ >}) = refl
        gen-inv (R2-d-a {μ = < suc _ , _ >}) = refl
        gen-inv (R2-d-b {μ = < zero  , _ >}) = refl
        gen-inv (R2-d-b {μ = < suc _ , _ >}) = refl
        gen-inv (R3) = refl
        gen-inv (R0-b-b {μ₁ = < zero  , _ >} {< zero  , _ >} i) = refl
        gen-inv (R0-b-b {μ₁ = < zero  , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-b-b {μ₁ = < suc _ , _ >} {< zero  , _ >} i) = refl
        gen-inv (R0-b-b {μ₁ = < suc _ , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-b-c {μ = < zero , _ >} i) = refl
        gen-inv (R0-b-c {μ = < suc _ , _ >} i) = refl
        gen-inv (R0-b-d {μ₁ = < zero , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-b-d {μ₁ = < zero , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-b-d {μ₁ = < suc _ , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-b-d {μ₁ = < suc _ , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-c-b {μ = < zero , _ >} i) = refl
        gen-inv (R0-c-b {μ = < suc _ , _ >} i) = refl
        gen-inv (R0-c-c i) = refl
        gen-inv (R0-c-d {μ = < zero , _ >} i) = refl
        gen-inv (R0-c-d {μ = < suc _ , _ >} i) = refl
        gen-inv (R0-d-b {μ₁ = < zero , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-d-b {μ₁ = < zero , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-d-b {μ₁ = < suc _ , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-d-b {μ₁ = < suc _ , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-d-c {μ = < zero , _ >} i) = refl
        gen-inv (R0-d-c {μ = < suc _ , _ >} i) = refl
        gen-inv (R0-d-d {μ₁ = < zero , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-d-d {μ₁ = < zero , _ >} {< suc _ , _ >} i) = refl
        gen-inv (R0-d-d {μ₁ = < suc _ , _ >} {< zero , _ >} i) = refl
        gen-inv (R0-d-d {μ₁ = < suc _ , _ >} {< suc _ , _ >} i) = refl

r-invar : Legn Pattern-Invariant r wrt _≡_
r-invar = cong half ∘ r×2-invar


w : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
w (idPat _) = 0
w (bGr _ _ x) = w x
w (dGr _ _ x) = w x
w {rs = rs} (cGr i x) = cPosty i rs + w x
  where cPosty : ∀ {n} (i : Fin (1 + n)) -> Vec (ℤmod 2) (2 + n) -> ℤ
        cPosty zero (< zero  , _ > ∷ < zero  , _ > ∷ _) = 1
        cPosty zero (< suc _ , _ > ∷ < suc _ , _ > ∷ _) = 1
        cPosty zero (_ ∷ _ ∷ _) = -1
        cPosty (suc ()) (_ ∷ _ ∷ [])
        cPosty (suc i) (x ∷ y ∷ z ∷ xs) = cPosty i (y ∷ z ∷ xs)


tb : ∀ {l} {ls : Vec _ l} -> PatternFD ls -> ℤ
tb x = w x + (ℤ.- half (cusps x))
  where cusps : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> TangleFD ls rs -> ℤ
        cusps (bGr _ _ x) = 1 + cusps x
        cusps (cGr _   x) =     cusps x
        cusps (dGr _ _ x) = 1 + cusps x
        cusps (idPat _)   = 0
