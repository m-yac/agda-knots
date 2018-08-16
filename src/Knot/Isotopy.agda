
module Knot.Isotopy where

open import Utils
open import Knot.FrontDiagram

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


_above_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (μ : ℤmod n)
          -> nGradedFD n ls rs -> nGradedFD n (μ ∷ ls) (μ ∷ rs)
μ above bGr i μ₁ x = bGr (suc i) μ₁ (μ above x)
μ above cGr i x = cGr (suc i) (μ above x)
μ above dGr i μ₁ x = dGr (suc i) μ₁ (μ above x)
μ above idPat ls = idPat (μ ∷ ls)


min-R1-a : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r}
           -> nGradedFD n (insert i μ rs) (insert i μ rs)
min-R1-a (suc i) {μ} {μ₁ ∷ rs} = μ₁ above (min-R1-a i)
min-R1-a (suc ()) {_} {[]}
min-R1-a zero {μ}
  = _ <: bGr' (# 0) μ , cGr (# 1) , dGr' (# 0) μ

min-R1-b : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r}
           -> nGradedFD n (insert i μ rs) (insert i μ rs)
min-R1-b (suc i) {μ} {μ₁ ∷ rs} = μ₁ above (min-R1-b i)
min-R1-b (suc ()) {_} {[]}
min-R1-b zero {μ}
  = _ <: bGr (# 1) μ , cGr (# 0) , dGr (# 1) μ


min-R2-nw : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert i μ rs) (insert2 (suc i) < μ' , dec μ' > (insert i μ rs))
min-R2-nw (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-nw i μ')
min-R2-nw (suc ()) {_} {[]} _
min-R2-nw zero μ'
  = _ <: bGr (# 0) μ' , cGr (# 1) , cGr (# 0)

min-R2-sw : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert i μ rs) (insert2 (at i) < μ' , dec μ' > (insert i μ rs))
min-R2-sw (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-sw i μ')
min-R2-sw (suc ()) {_} {[]} _
min-R2-sw zero μ'
  = _ <: bGr (# 1) μ' , cGr (# 0) , cGr (# 1)

min-R2-ne : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert2 (suc i) < μ' , dec μ' > (insert i μ rs)) (insert i μ rs)
min-R2-ne (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-ne i μ')
min-R2-ne (suc ()) {_} {[]} _
min-R2-ne zero μ'
  = _ <: cGr (# 0) , cGr (# 1) , dGr (# 0) μ'

min-R2-se : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert2 (at i) < μ' , dec μ' > (insert i μ rs)) (insert i μ rs)
min-R2-se (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-se i μ')
min-R2-se (suc ()) {_} {[]} _
min-R2-se zero μ'
  = _ <: cGr (# 1) , cGr (# 0) , dGr (# 1) μ'


min-R3-1 : ∀ {r n} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n} {rs : Vec _ r}
            -> nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)
min-R3-1 (suc i) {_} {_} {_} {μ₁ ∷ rs} = μ₁ above (min-R3-1 i)
min-R3-1 (suc ()) {_} {_} {_} {[]}
min-R3-1 zero
  = _ <: cGr (# 0) , cGr (# 1) , cGr (# 0)

min-R3-2 : ∀ {r n} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n} {rs : Vec _ r}
            -> nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)
min-R3-2 (suc i) {_} {_} {_} {μ₁ ∷ rs} = μ₁ above (min-R3-2 i)
min-R3-2 (suc ()) {_} {_} {_} {[]}
min-R3-2 zero
  = _ <: cGr (# 1) , cGr (# 0) , cGr (# 1)



min-R0-c-b : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (2 + r)} (μ : ℤmod n)
             -> nGradedFD n rs (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > (swap2 i rs))
min-R0-c-b zero () {rs} μ
min-R0-c-b (suc zero) () {rs} μ
min-R0-c-b (suc (suc i)) zero {rs} μ = _ <: bGr zero μ , cGr (suc (suc (suc (suc i))))
min-R0-c-b (suc (suc i)) (suc j) {μ₁ ∷ rs} μ = μ₁ above min-R0-c-b (suc i) j {rs} μ

min-R0-c-c : ∀ {r n} (i : Fin (3 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (4 + r)}
             -> nGradedFD n rs (swap2 (inj₋₁ i j) (swap2 i rs))
min-R0-c-c zero ()
min-R0-c-c (suc zero) ()
min-R0-c-c (suc (suc i)) zero {μ₃ ∷ μ₄ ∷ rs} = _ <: cGr zero , cGr (suc (suc i))
min-R0-c-c {zero} (suc (suc zero)) (suc ())
min-R0-c-c {zero} (suc (suc (suc ()))) (suc _)
min-R0-c-c {suc r} (suc (suc i)) (suc j) {μ ∷ rs} = μ above min-R0-c-c (suc i) j {rs}

min'-R0-c-d : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
                {rs : Vec (ℤmod n) (2 + r)} (μ : ℤmod n)
              -> nGradedFD n (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > rs) (swap2 i rs)
min'-R0-c-d zero () {rs} μ
min'-R0-c-d (suc zero) () {rs} μ
min'-R0-c-d (suc (suc i)) zero {rs} μ = _ <: cGr (suc (suc (suc (suc i)))) , dGr zero μ
min'-R0-c-d (suc (suc i)) (suc j) {μ₁ ∷ rs} μ = μ₁ above min'-R0-c-d (suc i) j {rs} μ



data RMove : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where
  ----------------
  -- R1 moves, both Above and Below
  R1-a : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
         -> {x : nGradedFD n ls (insert1 i μ rs)}
         -> RMove x (x + min-R1-a i)
  R1-b : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
         -> {x : nGradedFD n ls (insert1 i μ rs)}
         -> RMove x (x + min-R1-b i)
  ----------------
  -- R2 moves, with the cusp moving in the SW, NW, SE, and NE directions
  R2-nw : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert1 i μ rs)}
          -> RMove (x , bGr (suc i) μ') (x + min-R2-nw i μ')
  R2-sw : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert1 i μ rs)}
          -> RMove (x , bGr (at i) μ') (x + min-R2-sw i μ')
  R2-ne : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert2 (suc i) < μ' , dec μ' > (insert i μ rs))}
          -> RMove (x , dGr (suc i) μ') (x + min-R2-ne i μ')
  R2-se : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert2 (at i) < μ' , dec μ' > (insert i μ rs))}
          -> RMove (x , dGr (at i) μ') (x + min-R2-se i μ')
  ----------------
  -- R3 move
  R3 : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n}
       -> {x : nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)}
       -> RMove (x + min-R3-1 i) (x + min-R3-2 i)
  ----------------
  -- R0 moves, between each possible pairing of the events
  -- Notation: "R0-x-b i j" starts with 'x i' to the below-left of 'b j'
  --           "R0-x-c i j" starts with 'x (2+i)' to the below-left of 'c j'
  --           "R0-x-d i j" starts with 'x (2+i)' to the below-left of 'd j'
  R0-c-b : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ : ℤmod n} {x : nGradedFD n ls rs}
           -> RMove (x , cGr i , bGr (at (inj₋₁ _ j) up 2) μ) (x + min-R0-c-b i j μ)
  R0-c-c : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (4 + r)}
           -> (i : Fin (3 + r)) (j : Fin′ (pred i)) {x : nGradedFD n ls rs}
           -> RMove (x , cGr i , cGr (inj₋₁ _ j)) (x + min-R0-c-c i j)
  R0-c-d : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (4 + r)}
           -> (i : Fin (3 + r)) (j : Fin′ (pred i)) {μ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > rs)}
           -> RMove (x + min'-R0-c-d i j μ) (x , dGr (at (inj₋₁ i j) up 2) μ , cGr i)

data LegIso : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where
  doMoveBefore : ∀ {l m r n} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r} {Λ₁ Λ₂ : nGradedFD n ls ms}
               -> RMove Λ₁ Λ₂ -> (Λ′ : nGradedFD n ms rs) -> LegIso (Λ₁ + Λ′) (Λ₂ + Λ′)
  doMoveBefore' : ∀ {l m r n} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r} {Λ₁ Λ₂ : nGradedFD n ls ms}
                -> RMove Λ₂ Λ₁ -> (Λ′ : nGradedFD n ms rs) -> LegIso (Λ₁ + Λ′) (Λ₂ + Λ′)
  _then_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {Λ₁ Λ₂ Λ₃ : nGradedFD n ls rs}
           -> LegIso Λ₁ Λ₂ -> LegIso Λ₂ Λ₃ -> LegIso Λ₁ Λ₃
  Rrefl : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {Λ : nGradedFD n ls rs} -> LegIso Λ Λ

infixl 6 _then_

open import Data.Product as Σ using (Σ-syntax)

doAtIdx : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {Λ : nGradedFD n ls rs} (i : Fin (1 + len Λ))
         -> let < m , < ms , < Λl , Λr > > > = split Λ before i
             in {Λ₂ : nGradedFD n ls ms}
                -> RMove Λl Λ₂ -> LegIso Λ (Λ₂ + Λr)
doAtIdx {Λ = Λ} i {Λ₂} m
  = let Λr = Σ.proj₂ (Σ.proj₂ (Σ.proj₂ (split Λ before i)))
     in subst (\ z -> LegIso z (Λ₂ + Λr)) (sym (split-before-hcomp Λ i))
              (doMoveBefore m Λr)

syntax doAtIdx i m = m atIdx i

doAtIdx' : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {Λ : nGradedFD n ls rs} (i : Fin (1 + len Λ))
         -> let < m , < ms , < Λl , Λr > > > = split Λ before i
             in {Λ₂ : nGradedFD n ls ms}
                -> RMove Λ₂ Λl -> LegIso Λ (Λ₂ + Λr)
doAtIdx' {Λ = Λ} i {Λ₂} m
  = let Λr = Σ.proj₂ (Σ.proj₂ (Σ.proj₂ (split Λ before i)))
     in subst (\ z -> LegIso z (Λ₂ + Λr)) (sym (split-before-hcomp Λ i))
              (doMoveBefore' m Λr)

syntax doAtIdx' i m = inv m atIdx i


ex-R1 : LegIso ([] <: b+ 0 , d 0) ([] <: b+ 0 , b- 0 , c 1 , d 0 , d 0)
ex-R1 = Rrefl then (R1-a (# 0)) atIdx (# 1)


-- do-R1-b : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (suc r)) {μ : ℤmod n}
--           -> nGradedLegFD n ls (insert1 i μ rs) -> nGradedLegFD n ls (insert1 i μ rs)
-- do-R1-b {l} {r} {n} {ls} {rs} zero {μ} x
--   = x , bGr (suc zero) μ , cGr (at zero) , dGr (suc zero) μ
-- do-R1-b {l} {zero} {n} {ls} {rs} (suc ()) {μ} x
-- do-R1-b {l} {suc r} {n} {ls} {μ₁ ∷ rs} (suc i) {μ} x = x + (μ₁ above do-R1-b i (idPat (insert i μ rs)))
-- do-R1-b {l} {r} {n} {ls} {rs} i {μ} x
--   = x , bGr (suc i) μ , cGr (at i)
--       , subst (\ z -> nGradedLegFD _ _ z → nGradedLegFD _ _ (insert1 _ _ _)) (sym lem)
--               (dGr (suc i) μ)
--   where lem : swap2 (at i) (insert2 (suc i) < μ , dec μ > (insert1 i μ rs))
--               ≡ insert2 (suc i) < μ , dec μ > (insert i μ rs)
--         lem = begin
--           swap2 (at i) (insert2 (suc i) < μ , dec μ > (insert1 i μ rs))
--             ≡⟨ insert-swap2-comm i (insert (suc i) μ (insert i μ rs)) ⟩
--           insert (suc (suc i)) (dec μ) (swap2 i (insert (suc i) μ (insert i μ rs)))
--             ≡⟨ cong (insert _ _) (insert2-swap2-combn i rs) ⟩
--           insert2 (suc i) < μ , dec μ > (insert i μ rs)
--             ∎

-- do-R1-a : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (suc r)) {μ : ℤmod n}
--           -> nGradedLegFD n ls (insert1 i μ rs) -> nGradedLegFD n ls (insert1 i μ rs)
-- do-R1-a {l} {r} {n} {ls} {rs} i {μ} x
--   = x , bGr' (at i) μ , cGr (suc i)
--       , subst (\ z → nGradedLegFD _ _ z → nGradedLegFD _ _ (insert1 _ _ _)) (sym lem)
--               (dGr' (at i) μ)
--   where lem : swap2 (suc i) (insert2 (at i) < inc μ , μ > (insert1 i μ rs))
--               ≡ insert2 (at i) < inc μ , μ > (insert i μ rs)
--         lem = begin
--           swap2 (suc i) (insert2 (at i) < inc μ , μ > (insert1 i μ rs))
--             ≡⟨ cong (swap2 _) (insert2-insert-comm-at i rs) ⟩
--           swap2 (suc i) (insert2 (suc i) < μ , μ > (insert i (inc μ) rs))
--             ≡⟨ insert2-swap2-combn (suc i) (insert i (inc μ) rs) ⟩
--           insert2 (suc i) (< μ , μ >) (insert i (inc μ) rs)
--             ≡⟨ sym (insert2-insert-comm-at i rs) ⟩
--           insert2 (at i) < inc μ , μ > (insert i μ rs)
--             ∎
