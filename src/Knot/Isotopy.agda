
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
  = _ <: bGr' 0 μ , cGr 1 , dGr' 0 μ

min-R1-b : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r}
           -> nGradedFD n (insert i μ rs) (insert i μ rs)
min-R1-b (suc i) {μ} {μ₁ ∷ rs} = μ₁ above (min-R1-b i)
min-R1-b (suc ()) {_} {[]}
min-R1-b zero {μ}
  = _ <: bGr 1 μ , cGr 0 , dGr 1 μ


min-R2-b-a : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert i μ rs) (insert2 (at i) < μ' , dec μ' > (insert i μ rs))
min-R2-b-a (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-b-a i μ')
min-R2-b-a (suc ()) {_} {[]} _
min-R2-b-a zero μ'
  = _ <: bGr 1 μ' , cGr 0 , cGr 1

min-R2-b-b : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert i μ rs) (insert2 (suc i) < μ' , dec μ' > (insert i μ rs))
min-R2-b-b (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-b-b i μ')
min-R2-b-b (suc ()) {_} {[]} _
min-R2-b-b zero μ'
  = _ <: bGr 0 μ' , cGr 1 , cGr 0

min-R2-d-a : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert2 (at i) < μ' , dec μ' > (insert i μ rs)) (insert i μ rs)
min-R2-d-a (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-d-a i μ')
min-R2-d-a (suc ()) {_} {[]} _
min-R2-d-a zero μ'
  = _ <: cGr 1 , cGr 0 , dGr 1 μ'

min-R2-d-b : ∀ {r n} (i : Fin (1 + r)) {μ : ℤmod n} {rs : Vec _ r} (μ' : ℤmod n)
            -> nGradedFD n (insert2 (suc i) < μ' , dec μ' > (insert i μ rs)) (insert i μ rs)
min-R2-d-b (suc i) {μ} {μ₁ ∷ rs} μ' = μ₁ above (min-R2-d-b i μ')
min-R2-d-b (suc ()) {_} {[]} _
min-R2-d-b zero μ'
  = _ <: cGr 0 , cGr 1 , dGr 0 μ'


min-R3-1 : ∀ {r n} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n} {rs : Vec _ r}
            -> nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)
min-R3-1 (suc i) {_} {_} {_} {μ₁ ∷ rs} = μ₁ above (min-R3-1 i)
min-R3-1 (suc ()) {_} {_} {_} {[]}
min-R3-1 zero
  = _ <: cGr 0 , cGr 1 , cGr 0

min-R3-2 : ∀ {r n} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n} {rs : Vec _ r}
            -> nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)
min-R3-2 (suc i) {_} {_} {_} {μ₁ ∷ rs} = μ₁ above (min-R3-2 i)
min-R3-2 (suc ()) {_} {_} {_} {[]}
min-R3-2 zero
  = _ <: cGr 1 , cGr 0 , cGr 1



min-R0-b-b : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) r} (μ₁ μ₂ : ℤmod n)
             -> nGradedFD n rs (insert2 (suc (suc i)) < μ₂ , dec μ₂ > (insert2 (inj₋₁ i j) < μ₁ , dec μ₁ > rs))
min-R0-b-b zero () {rs} μ₁ μ₂
min-R0-b-b (suc zero) () {rs} μ₁ μ₂
min-R0-b-b (suc (suc i)) zero {rs} μ₁ μ₂ = _ <: bGr (suc (suc i)) μ₂ , bGr zero μ₁
min-R0-b-b (suc (suc i)) (suc j) {μ ∷ rs} μ₁ μ₂ = μ above min-R0-b-b (suc i) j {rs} μ₁ μ₂

min-R0-b-c : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (2 + r)} (μ : ℤmod n)
             -> nGradedFD n rs (insert2 (at i up 2) < μ , dec μ > (swap2 (inj₋₁ i j) rs))
min-R0-b-c zero () {rs} μ
min-R0-b-c (suc zero) () {rs} μ
min-R0-b-c (suc (suc i)) zero {μ₃ ∷ μ₄ ∷ rs} μ = _ <: bGr (at (suc (suc i)) up 2) μ , cGr zero
min-R0-b-c (suc (suc i)) (suc j) {μ₁ ∷ rs} μ = μ₁ above min-R0-b-c (suc i) j {rs} μ

min-R0-b-d : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) r} (μ₁ μ₂ : ℤmod n)
             -> nGradedFD n (insert2 (inj₋₁ i j) < μ₁ , dec μ₁ > rs) (insert2 i < μ₂ , dec μ₂ > rs)
min-R0-b-d zero () {rs} μ₁ μ₂
min-R0-b-d (suc zero) () {rs} μ₁ μ₂
min-R0-b-d (suc (suc i)) zero {rs} μ₁ μ₂ = _ <: bGr (suc (suc (suc (suc i)))) μ₂ , dGr zero μ₁
min-R0-b-d (suc (suc i)) (suc j) {μ ∷ rs} μ₁ μ₂ = μ above min-R0-b-d (suc i) j {rs} μ₁ μ₂

min-R0-c-b : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (2 + r)} (μ : ℤmod n)
             -> nGradedFD n rs (swap2 (suc (suc i)) (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > rs))
min-R0-c-b zero () {rs} μ
min-R0-c-b (suc zero) () {rs} μ
min-R0-c-b (suc (suc i)) zero {rs} μ = _ <: cGr (suc (suc i)) , bGr zero μ
min-R0-c-b (suc (suc i)) (suc j) {μ₁ ∷ rs} μ = μ₁ above min-R0-c-b (suc i) j {rs} μ

min-R0-c-c : ∀ {r n} (i : Fin (3 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (4 + r)}
             -> nGradedFD n rs (swap2 i (swap2 (inj₋₁ i j) rs))
min-R0-c-c zero ()
min-R0-c-c (suc zero) ()
min-R0-c-c (suc (suc i)) zero {μ₃ ∷ μ₄ ∷ rs} = _ <: cGr (suc (suc i)) , cGr zero
min-R0-c-c {zero} (suc (suc zero)) (suc ())
min-R0-c-c {zero} (suc (suc (suc ()))) (suc _)
min-R0-c-c {suc r} (suc (suc i)) (suc j) {μ ∷ rs} = μ above min-R0-c-c (suc i) j {rs}

min-R0-c-d : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
                {rs : Vec (ℤmod n) (2 + r)} (μ : ℤmod n)
              -> nGradedFD n (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > rs) (swap2 i rs)
min-R0-c-d zero () {rs} μ
min-R0-c-d (suc zero) () {rs} μ
min-R0-c-d (suc (suc i)) zero {rs} μ = _ <: cGr (suc (suc (suc (suc i)))) , dGr zero μ
min-R0-c-d (suc (suc i)) (suc j) {μ₁ ∷ rs} μ = μ₁ above min-R0-c-d (suc i) j {rs} μ

min-R0-d-b : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) r} (μ₁ μ₂ : ℤmod n)
             -> nGradedFD n (insert2 i < μ₁ , dec μ₁ > rs) (insert2 (inj₋₁ i j) < μ₂ , dec μ₂ > rs)
min-R0-d-b zero () {rs} μ₁ μ₂
min-R0-d-b (suc zero) () {rs} μ₁ μ₂
min-R0-d-b (suc (suc i)) zero {rs} μ₁ μ₂ = _ <: bGr zero μ₂ , dGr (suc (suc (suc (suc i)))) μ₁
min-R0-d-b (suc (suc i)) (suc j) {μ ∷ rs} μ₁ μ₂ = μ above min-R0-d-b (suc i) j {rs} μ₁ μ₂

min-R0-d-c : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) (2 + r)} (μ₁ μ₂ : ℤmod n)
             -> nGradedFD n (insert2 (suc (suc i)) < μ₁ , dec μ₁ > rs) (swap2 (inj₋₁ i j) rs)
min-R0-d-c zero () {rs} μ₁ μ₂
min-R0-d-c (suc zero) () {rs} μ₁ μ₂
min-R0-d-c (suc (suc i)) zero {μ₃ ∷ μ₄ ∷ rs} μ₁ μ₂ = _ <: cGr zero , dGr (suc (suc (suc (suc i)))) μ₁
min-R0-d-c (suc (suc i)) (suc j) {μ ∷ rs} μ₁ μ₂ = μ above min-R0-d-c (suc i) j {rs} μ₁ μ₂

min-R0-d-d : ∀ {r n} (i : Fin (1 + r)) (j : Fin′ (pred i))
               {rs : Vec (ℤmod n) r} (μ₁ μ₂ : ℤmod n)
             -> nGradedFD n (insert2 (suc (suc i)) < μ₁ , dec μ₁ > (insert2 (inj₋₁ i j) < μ₂ , dec μ₂ > rs)) rs
min-R0-d-d zero () {rs} μ₁ μ₂
min-R0-d-d (suc zero) () {rs} μ₁ μ₂
min-R0-d-d (suc (suc i)) zero {rs} μ₁ μ₂ = _ <: dGr zero μ₂ , dGr (suc (suc i)) μ₁
min-R0-d-d (suc (suc i)) (suc j) {μ ∷ rs} μ₁ μ₂ = μ above min-R0-d-d (suc i) j {rs} μ₁ μ₂


infix 2 _~′_

data _~′_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where
  ----------------
  -- R1 moves, both Above and Below
  R1-a : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
         -> {x : nGradedFD n ls (insert1 i μ rs)}
         -> x ~′ x + min-R1-a i
  R1-b : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
         -> {x : nGradedFD n ls (insert1 i μ rs)}
         -> x ~′ x + min-R1-b i
  ----------------
  -- R2 moves, with B and D cusps both Above and Below
  R2-b-a : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert1 i μ rs)}
          -> x , bGr (at i) μ' ~′ x + min-R2-b-a i μ'
  R2-b-b : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert1 i μ rs)}
          -> x , bGr (suc i) μ' ~′ x + min-R2-b-b i μ'
  R2-d-a : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert2 (at i) < μ' , dec μ' > (insert i μ rs))}
          -> x , dGr (at i) μ' ~′ x + min-R2-d-a i μ'
  R2-d-b : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (i : Fin (1 + r)) {μ : ℤmod n}
          -> (μ' : ℤmod n) {x : nGradedFD n ls (insert2 (suc i) < μ' , dec μ' > (insert i μ rs))}
          -> x , dGr (suc i) μ' ~′ x + min-R2-d-b i μ'
  ----------------
  -- R3 move
  R3 : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r} (i : Fin (1 + r)) {μ₁ μ₂ μ₃ : ℤmod n}
       -> {x : nGradedFD n (insert3 i < μ₁ , < μ₂ , μ₃ > > rs) (insert3 i < μ₃ , < μ₂ , μ₁ > > rs)}
       -> x + min-R3-1 i ~′ x + min-R3-2 i
  ----------------
  -- R0 moves, between each possible pairing of the events - see above
  -- Notation: "R0-x-b i j" starts with 'x i' to the below-left of 'b j'
  --           "R0-x-c i j" starts with 'x (2+i)' to the below-left of 'c j'
  --           "R0-x-d i j" starts with 'x (2+i)' to the below-left of 'd j'
  R0-b-b : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ₁ μ₂ : ℤmod n} {x : nGradedFD n ls rs}
           -> x + min-R0-b-b i j μ₁ μ₂ ~′ x , bGr (inj₋₁ i j) μ₁ , bGr (suc (suc i)) μ₂
  R0-b-c : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ : ℤmod n} {x : nGradedFD n ls rs}
           -> x + min-R0-b-c i j μ ~′ x , cGr (inj₋₁ i j) , bGr (at i up 2) μ
  R0-b-d : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ₁ μ₂ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 (inj₋₁ i j) < μ₁ , dec μ₁ > rs)}
           -> x + min-R0-b-d i j μ₁ μ₂ ~′ x , dGr (inj₋₁ i j) μ₁ , bGr i μ₂
  R0-c-b : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ : ℤmod n} {x : nGradedFD n ls rs}
           -> x + min-R0-c-b i j μ ~′ x , bGr (at (inj₋₁ i j) up 2) μ , cGr (suc (suc i))
  R0-c-c : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (4 + r)}
           -> (i : Fin (3 + r)) (j : Fin′ (pred i)) {x : nGradedFD n ls rs}
           -> x + min-R0-c-c i j ~′ x , cGr (inj₋₁ i j) , cGr i
  R0-c-d : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (4 + r)}
           -> (i : Fin (3 + r)) (j : Fin′ (pred i)) {μ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 (at (inj₋₁ i j) up 2) < μ , dec μ > rs)}
           -> x + min-R0-c-d i j μ ~′ x , dGr (at (inj₋₁ i j) up 2) μ , cGr i
  R0-d-b : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ₁ μ₂ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 i < μ₁ , dec μ₁ > rs)}
           -> x , dGr i μ₁ , bGr (inj₋₁ i j) μ₂ ~′ x + min-R0-d-b i j μ₁ μ₂
  R0-d-c : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ₁ μ₂ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 (suc (suc i)) < μ₁ , dec μ₁ > rs)}
           -> x , dGr (suc (suc i)) μ₁ , cGr (inj₋₁ i j) ~′ x + min-R0-d-c i j μ₁ μ₂
  R0-d-d : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
           -> (i : Fin (1 + r)) (j : Fin′ (pred i)) {μ₁ μ₂ : ℤmod n}
           -> {x : nGradedFD n ls (insert2 (suc (suc i)) < μ₁ , dec μ₁ > (insert2 (inj₋₁ i j) < μ₂ , dec μ₂ > rs))}
           -> x , dGr (suc (suc i)) μ₁ , dGr (inj₋₁ i j) μ₂ ~′ x + min-R0-d-d i j μ₁ μ₂

open import Relation.Binary.Closure.Equivalence
open import Relation.Binary.Core as Bin using (Rel; _⇒_; _=[_]⇒_; IsEquivalence)

infix 2 _~_

data _~_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where
  doAtIdx : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {Λ : nGradedFD n ls rs} (i : Fin (1 + len Λ))
             -> let < m , < ms , < Λl , Λr > > > = split Λ before i
                 in {Λ' : nGradedFD n ls ms} -> Λl ~′ Λ' -> Λ       ~ Λ' + Λr
                                        -- AKA: Λl ~′ Λ' -> Λl + Λr ~′ Λ' + Λr

syntax doAtIdx i m = m atIdx i

LegIso : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set
LegIso = EqClosure _~_

open import Relation.Binary.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Data.Sum as Sum using (_⊎_)
open Sum public using () renaming (inj₁ to fwd; inj₂ to bwd)

EqClosureEq : ∀ {a ℓ} {A : Set a} {P : Rel A ℓ} {{isEquiv : IsEquivalence P}} -> EqClosure P ⇒ P
EqClosureEq {{isEquiv = pf}} ε            = IsEquivalence.refl  pf
EqClosureEq {{isEquiv = pf}} (fwd x ◅ xs) = IsEquivalence.trans pf                       x  (EqClosureEq xs)
EqClosureEq {{isEquiv = pf}} (bwd x ◅ xs) = IsEquivalence.trans pf (IsEquivalence.sym pf x) (EqClosureEq xs)



ex-R1 : LegIso ([] <: b+ 0 , d 0) ([] <: b+ 0 , b- 0 , c 1 , d 0 , d 0)
ex-R1 = fwd (doAtIdx 1 (R1-a 0)) ◅ ε


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
