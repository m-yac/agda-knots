
module Knot.Isotopy where

open import Utils
open import Knot.FrontDiagram

open import Data.Product as Σ using (Σ-syntax)
open import Relation.Binary.Closure.Symmetric
open import Relation.Binary.Closure.ReflexiveTransitive using (ε; _◅_) renaming (Star to ReflTransClosure)
open import Data.Sum as Sum using (_⊎_) renaming (inj₁ to fwd; inj₂ to bwd)



data IsoType : ℕ -> Set where
  -- Legendrian Isotopy on tangles of arbitrary grading
  Legn : ∀ {n} -> IsoType n
  -- Smooth Isotopy on oriented tangles
  OriSmth : IsoType 2
  -- Smooth Isotopy on unoriented tangles
  UnOriSmth : IsoType 1


-- Generators of the Legendrian or Smooth Isotopy relation
data _Gen : ∀ {n} (ty : IsoType n) {l r} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where

  -- Reidemeister Type 1 moves, both [a]bove and [b]elow
  
  R1-a : ∀ {n ty} {μ : ℤmod n} {l} {μls : Vec _ l} -> let ls = μ ∷ μls in
         (ty Gen) (idPat ls) (ls <: bGr' 0 μ , cGr 1 , dGr' 0 μ)

  R1-b : ∀ {n ty} {μ : ℤmod n} {l} {μls : Vec _ l} -> let ls = μ ∷ μls in
         (ty Gen) (idPat ls) (ls <: bGr  1 μ , cGr 0 , dGr  1 μ)

  -- Reidemeister Type 2 moves, with [d] and [d] cusps both [a]bove and [b]elow
  
  R2-b-a : ∀ {n ty} {μ μl : ℤmod n} {l} {μls : Vec _ l} -> let ls = μl ∷ μls in
           (ty Gen) (ls <: bGr 0 μ) (ls <: bGr 1 μ , cGr 0 , cGr 1)

  R2-b-b : ∀ {n ty} {μ μl : ℤmod n} {l} {μls : Vec _ l} -> let ls = μl ∷ μls in
           (ty Gen) (ls <: bGr 1 μ) (ls <: bGr 0 μ , cGr 1 , cGr 0)

  R2-d-a : ∀ {n ty} {μ μr : ℤmod n} {l} {μls : Vec _ l} -> let ls = insert2 0 < μ , dec μ > (μr ∷ μls) in
           (ty Gen) (ls <: dGr 0 μ) (ls <: cGr 1 , cGr 0 , dGr 1 μ)

  R2-d-b : ∀ {n ty} {μ μr : ℤmod n} {l} {μls : Vec _ l} -> let ls = insert2 1 < μ , dec μ > (μr ∷ μls) in
           (ty Gen) (ls <: dGr 1 μ) (ls <: cGr 0 , cGr 1 , dGr 0 μ)

  -- Reidemeister Type 3 move
  
  R3 : ∀ {n ty} {μl₀ μl₁ μl₂ : ℤmod n} {l} {μls : Vec _ l} -> let ls = μl₀ ∷ μl₁ ∷ μl₂ ∷ μls in
       (ty Gen) (ls <: cGr 0 , cGr 1 , cGr 0) (ls <: cGr 1 , cGr 0 , cGr 1)

  -- Reidemeister 0 moves - all permissible exchanges between b's, c's, and d's
  
  R0-b-b : ∀ {n ty} {μ₁ μ₂ : ℤmod n} {l} {ls : Vec _ l} (i : Fin (1 + l)) ->
           (ty Gen) (ls <: bGr 0 μ₁ , bGr (suc (suc i)) μ₂) (ls <: bGr i μ₂ , bGr 0 μ₁)

  R0-b-c : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} {l} {ls : Vec _ (2 + l)} (i : Fin (1 + l)) ->
           (ty Gen) (ls <: bGr 0 μ , cGr (suc (suc i))) (ls <: cGr i , bGr 0 μ)

  R0-b-d : ∀ {n ty} {μ₁ μ₂ : ℤmod n} {l} {μls : Vec _ l} (i : Fin (1 + l)) -> let ls = insert2 i < μ₂ , dec μ₂ > μls in
           (ty Gen) (ls <: bGr 0 μ₁ , dGr (suc (suc i)) μ₂) (ls <: dGr i μ₂ , bGr 0 μ₁)

  R0-c-b : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} {l} {μls : Vec _ l} (i : Fin (1 + l)) -> let ls = μl₀ ∷ μl₁ ∷ μls in
           (ty Gen) (ls <: cGr 0 , bGr (suc (suc i)) μ) (ls <: bGr (suc (suc i)) μ , cGr 0)

  R0-c-c : ∀ {n ty} {μl₀ μl₁ : ℤmod n} {l} {μls : Vec _ (2 + l)} (i : Fin (1 + l)) -> let ls = μl₀ ∷ μl₁ ∷ μls in
           (ty Gen) (ls <: cGr 0 , cGr (suc (suc i))) (ls <: cGr (suc (suc i)) , cGr 0)

  R0-c-d : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} {l} {μls : Vec _ l} (i : Fin (1 + l)) -> let ls = μl₀ ∷ μl₁ ∷ insert2 i < μ , dec μ > μls in
           (ty Gen) (ls <: cGr 0 , dGr (suc (suc i)) μ) (ls <: dGr (suc (suc i)) μ , cGr {rs = μl₀ ∷ μl₁ ∷ μls} 0) -- the type checker just needed some help!

  R0-d-b : ∀ {n ty} {μ₁ μ₂ : ℤmod n} {l} {μls : Vec _ l} (i : Fin (1 + l)) -> let ls = insert2 0 < μ₁ , dec μ₁ > μls in
           (ty Gen) (ls <: dGr 0 μ₁ , bGr i μ₂) (ls <: bGr (suc (suc i)) μ₂ , dGr 0 μ₁)

  R0-d-c : ∀ {n ty} {μ : ℤmod n} {l} {μls : Vec _ (2 + l)} (i : Fin (1 + l)) -> let ls = insert2 0 < μ , dec μ > μls in
           (ty Gen) (ls <: dGr 0 μ , cGr i) (ls <: cGr (suc (suc i)) , dGr 0 μ)

  R0-d-d : ∀ {n ty} {μ₁ μ₂ : ℤmod n} {l} {μls : Vec _ l} (i : Fin (1 + l)) -> let ls = insert2 0 < μ₁ , dec μ₁ > (insert2 i < μ₂ , dec μ₂ > μls) in
           (ty Gen) (ls <: dGr 0 μ₁ , dGr i μ₂) (ls <: dGr (suc (suc i)) μ₂ , dGr 0 μ₁)

  -- Oriented (Smooth) Stabilizations, both [a]bove and [b]elow
  
  o-Stb-a : ∀ {l} {μls : Vec (ℤmod 2) l} -> let ls = 0 ∷ μls in
            (OriSmth Gen) (idPat ls) (ls <: bGr 0 0 , dGr' 1 0)
            
  o+Stb-a : ∀ {l} {μls : Vec (ℤmod 2) l} -> let ls = 1 ∷ μls in
            (OriSmth Gen) (idPat ls) (ls <: bGr 0 1 , dGr' 1 1)
            
  o-Stb-b : ∀ {l} {μls : Vec (ℤmod 2) l} -> let ls = 0 ∷ μls in
            (OriSmth Gen) (idPat ls) (ls <: bGr' 1 0 , dGr 0 0)
            
  o+Stb-b : ∀ {l} {μls : Vec (ℤmod 2) l} -> let ls = 1 ∷ μls in
            (OriSmth Gen) (idPat ls) (ls <: bGr' 1 1 , dGr 0 1)

  -- Unoriented (Smooth) Stabilizations, both [a]bove and [b]elow
  
  uoStb-a : ∀ {l} {μls : Vec (ℤmod 1) l} -> let ls = 0 ∷ μls in
            (UnOriSmth Gen) (idPat ls) (ls <: bGr 0 0 , dGr' 1 0)
            
  uoStb-b : ∀ {l} {μls : Vec (ℤmod 1) l} -> let ls = 0 ∷ μls in
            (UnOriSmth Gen) (idPat ls) (ls <: bGr' 1 0 , dGr 0 0)


infix 1 _~_

-- The core of the Legendrian/Smooth Isotopy relation: arbitrary embeddings of the above
--  generators, or their symmetric counterparts, in larger tangles
data _~_ {n ty} : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set where
  _below_btwn_,_ : ∀ {ml mr} {mls : Vec _ ml} {mrs : Vec _ mr} {Λ₁ Λ₂ : nGradedFD n mls mrs}
  {-        do: -} -> SymClosure (ty Gen) Λ₁ Λ₂
  {-     below: -} -> ∀ {t} (ts : Vec (ℤmod n) t)
  {-   between: -} -> ∀ {l} {ls : Vec _ l} (Λl : nGradedFD n ls (ts ++ mls))
  {-     (and:) -} -> ∀ {r} {rs : Vec _ r} (Λr : nGradedFD n (ts ++ mrs) rs)
                   -> Λl + ts above Λ₁ + Λr  ~  Λl + ts above Λ₂ + Λr

-- The actual Legendrian/Smooth Isotopy relation: the reflexive/transitive closure of ~
_Iso : ∀ {n} (ty : IsoType n) {l r} {ls : Vec _ l} {rs : Vec _ r} (_ _ : nGradedFD n ls rs) -> Set
_Iso {n} ty = ReflTransClosure (_~_ {n} {ty})



ex-R1 : (Legn Iso) ([] <: b+ 0 , d 0) _
ex-R1 = (fwd R1-b       below ([] , gr _) btwn (_ <: b+ 0) , (_ <: d 0)) ◅
        (bwd (R0-d-d 0) below [] btwn ([] <: b+ 0 , b- 2 , c 1) , idPat []) ◅ ε




-- (For later:)
-- open import Relation.Binary.Core as Bin using (Rel; _⇒_; _=[_]⇒_; IsEquivalence)
-- ReflTransClosureEq : ∀ {a ℓ} {A : Set a} {P : Rel A ℓ} {{isEquiv : IsEquivalence P}} -> ReflTransClosure P ⇒ P
-- ReflTransClosureEq {{isEquiv = pf}} ε        = IsEquivalence.refl  pf
-- ReflTransClosureEq {{isEquiv = pf}} (x ◅ xs) = IsEquivalence.trans pf x (ReflTransClosureEq xs)
