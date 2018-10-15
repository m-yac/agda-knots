{-# OPTIONS --rewriting #-}

module Knot.Isotopy where

open import Knot.Prelude
open import Knot.FrontDiagram
open import Knot.FrontDiagram.Properties
open import Category.Monoidal.Closure

open import Relation.Binary.Closure.Symmetric as SymClosure using (SymClosure)
open import Relation.Binary.Closure.ReflexiveTransitive as ReflTransClosure using (ε) renaming (Star to ReflTransClosure; _◅_ to _∷ᵗ_; _◅◅_ to _++ᵗ_)
open import Relation.Binary
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)


data IsoType : ℕ -> Set where
  -- Legendrian Isotopy on tangles of arbitrary grading
  Legn : ∀ {n} -> IsoType n
  -- Smooth Isotopy on oriented tangles
  OriSmth : IsoType 2
  -- Smooth Isotopy on unoriented tangles
  UnOriSmth : IsoType 1


-- Generators of the Legendrian or Smooth Isotopy relation
data _Gen : ∀ {n} (ty : IsoType n) {ls rs} (_ _ : nGradedFD n ls rs) -> Set where

  -- Reidemeister Type 1 moves, both [a]bove and [b]elow
  
  R1-a : ∀ {n ty} {μ : ℤmod n} -> let ls = (dec μ) ∷ [] in
         (ty Gen) (idPat < _ , ls >) (ls <: bGr 0 μ , cGr 1 , dGr 0 μ)

  R1-b : ∀ {n ty} {μ : ℤmod n} -> let ls = μ ∷ [] in
         (ty Gen) (idPat < _ , ls >) (ls <: bGr 1 μ , cGr 0 , dGr 1 μ)

  -- Reidemeister Type 2 moves, with [b] and [d] cusps both [a]bove and [b]elow
  
  R2-b-a : ∀ {n ty} {μ μl : ℤmod n} -> let ls = μl ∷ [] in
           (ty Gen) (ls <: bGr 0 μ) (ls <: bGr 1 μ , cGr 0 , cGr 1)

  R2-b-b : ∀ {n ty} {μ μl : ℤmod n} -> let ls = μl ∷ [] in
           (ty Gen) (ls <: bGr 1 μ) (ls <: bGr 0 μ , cGr 1 , cGr 0)

  R2-d-a : ∀ {n ty} {μ μr : ℤmod n} -> let ls = insert2 0 < μ , dec μ > (μr ∷ []) in
           (ty Gen) (ls <: dGr 0 μ) (ls <: cGr 1 , cGr 0 , dGr 1 μ)

  R2-d-b : ∀ {n ty} {μ μr : ℤmod n} -> let ls = insert2 1 < μ , dec μ > (μr ∷ []) in
           (ty Gen) (ls <: dGr 1 μ) (ls <: cGr 0 , cGr 1 , dGr 0 μ)

  -- Reidemeister Type 3 move
  
  R3 : ∀ {n ty} {μl₀ μl₁ μl₂ : ℤmod n} -> let ls = μl₀ ∷ μl₁ ∷ μl₂ ∷ [] in
       (ty Gen) (ls <: cGr 0 , cGr 1 , cGr 0) (ls <: cGr 1 , cGr 0 , cGr 1)

  -- Reidemeister 0 moves - all permissible exchanges between b's, c's, and d's
  
  R0-b-b : ∀ {n ty} {μ₁ μ₂ : ℤmod n} (k : ℕ) {ls : Vec _ k} ->
           (ty Gen) (ls <: bGr 0 μ₁ , bGr (fromℕ (2 + k)) μ₂) (ls <: bGr (fromℕ k) μ₂ , bGr 0 μ₁)

  R0-b-c : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} (k : ℕ) {ls : Vec _ (2 + k)} ->
           (ty Gen) (ls <: bGr 0 μ , cGr (fromℕ (2 + k))) (ls <: cGr (fromℕ k) , bGr 0 μ)

  R0-b-d : ∀ {n ty} {μ₁ μ₂ : ℤmod n} (k : ℕ) {μls : Vec _ k} -> let ls = insert2 (fromℕ k) < μ₂ , dec μ₂ > μls in
           (ty Gen) (ls <: bGr 0 μ₁ , dGr (fromℕ (2 + k)) μ₂) (ls <: dGr (fromℕ k) μ₂ , bGr 0 μ₁)

  R0-c-b : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} (k : ℕ) {μls : Vec _ k} -> let ls = μl₀ ∷ μl₁ ∷ μls in
           (ty Gen) (ls <: cGr 0 , bGr (fromℕ (2 + k)) μ) (ls <: bGr (fromℕ (2 + k)) μ , cGr 0)

  R0-c-c : ∀ {n ty} {μl₀ μl₁ : ℤmod n} (k : ℕ) {μls : Vec _ (2 + k)} -> let ls = μl₀ ∷ μl₁ ∷ μls in
           (ty Gen) (ls <: cGr 0 , cGr (fromℕ (2 + k))) (ls <: cGr (fromℕ (2 + k)) , cGr 0)

  R0-c-d : ∀ {n ty} {μ μl₀ μl₁ : ℤmod n} (k : ℕ) {μls : Vec _ k} -> let ls = μl₀ ∷ μl₁ ∷ insert2 (fromℕ k) < μ , dec μ > μls in
           (ty Gen) (ls <: cGr 0 , dGr (fromℕ (2 + k)) μ) (ls <: dGr (fromℕ (2 + k)) μ , cGr {rs = μl₀ ∷ μl₁ ∷ μls} 0)
                                                                                       -- ^ the type checker just needed some help!
  R0-d-b : ∀ {n ty} {μ₁ μ₂ : ℤmod n} (k : ℕ) {μls : Vec _ k} -> let ls = insert2 0 < μ₁ , dec μ₁ > μls in
           (ty Gen) (ls <: dGr 0 μ₁ , bGr (fromℕ k) μ₂) (ls <: bGr (fromℕ (2 + k)) μ₂ , dGr 0 μ₁)

  R0-d-c : ∀ {n ty} {μ : ℤmod n} (k : ℕ) {μls : Vec _ (2 + k)} -> let ls = insert2 0 < μ , dec μ > μls in
           (ty Gen) (ls <: dGr 0 μ , cGr (fromℕ k)) (ls <: cGr (fromℕ (2 + k)) , dGr 0 μ)

  R0-d-d : ∀ {n ty} {μ₁ μ₂ : ℤmod n} (k : ℕ) {μls : Vec _ k} -> let ls = insert2 0 < μ₁ , dec μ₁ > (insert2 (fromℕ k) < μ₂ , dec μ₂ > μls) in
           (ty Gen) (ls <: dGr 0 μ₁ , dGr (fromℕ k) μ₂) (ls <: dGr (fromℕ (2 + k)) μ₂ , dGr 0 μ₁)

  -- Oriented (Smooth) Stabilizations, both [a]bove and [b]elow
  
  o-Stb-a : let ls = 0 ∷ [] in
            (OriSmth Gen) (idPat < _ , ls >) (ls <: bGr 0 0 , dGr 1 1)
            
  o+Stb-a : let ls = 1 ∷ [] in
            (OriSmth Gen) (idPat < _ , ls >) (ls <: bGr 0 1 , dGr 1 0)
            
  o-Stb-b : let ls = 0 ∷ [] in
            (OriSmth Gen) (idPat < _ , ls >) (ls <: bGr 1 1 , dGr 0 0)
            
  o+Stb-b : let ls = 1 ∷ [] in
            (OriSmth Gen) (idPat < _ , ls >) (ls <: bGr 1 0 , dGr 0 1)

  -- Unoriented (Smooth) Stabilizations, both [a]bove and [b]elow
  
  uoStb-a : let ls = 0 ∷ [] in
            (UnOriSmth Gen) (idPat < _ , ls >) (ls <: bGr 0 0 , dGr 1 0)
            
  uoStb-b : let ls = 0 ∷ [] in
            (UnOriSmth Gen) (idPat < _ , ls >) (ls <: bGr 1 0 , dGr 0 0)


-- The Legendrian/Smooth Isotopy relation: the reflexive/transitive closure
--  of the monoidal closure of the symmetric closure of the above set of generators (phew!)
_Iso : ∀ {n} (ty : IsoType n) {ls rs} (_ _ : nGradedFD n ls rs) -> Set
_Iso ty = ReflTransClosure (MonoidalClosure (SymClosure (ty Gen)))


-- We can embed isotopy arbitrarily in larger tangles

_∙ᵗˡ_ : ∀ {n} {ty : IsoType n} {ls ms₁ ms₂} {Λ₁ Λ₂ : nGradedFD n ms₁ ms₂}
        -> (Λ : nGradedFD n ls ms₁) -> (ty Iso) Λ₁ Λ₂ -> (ty Iso) (Λ ∙ Λ₁) (Λ ∙ Λ₂)
Λ ∙ᵗˡ ε = ε
Λ ∙ᵗˡ (emb {ms₁'} {ms₂'} {Λ₁'} {Λ₂'} p as bs Λl Λr ∷ᵗ ps) = p' ∷ᵗ (Λ ∙ᵗˡ ps)
  where eq : ∀ (Λᵢ : nGradedFD _ ms₁' ms₂') -> Λ ∙ Λl ∙ as ◅ Λᵢ ▻ bs ∙ Λr ≡ (Λ ∙ Λl) ∙ as ◅ Λᵢ ▻ bs ∙ Λr
        eq Λᵢ = sym (∙-assoc Λ Λl (as ◅ Λᵢ ▻ bs ∙ Λr))
        p' : MonoidalClosure _ (Λ ∙ Λl ∙ as ◅ Λ₁' ▻ bs ∙ Λr) (Λ ∙ Λl ∙ as ◅ Λ₂' ▻ bs ∙ Λr)
        p' rewrite eq Λ₁' | eq Λ₂' = emb p as bs (Λ ∙ Λl) Λr
infixr 5 _∙ᵗˡ_

_∙ᵗʳ_ : ∀ {n} {ty : IsoType n} {rs ms₁ ms₂} {Λ₁ Λ₂ : nGradedFD n ms₁ ms₂}
        -> (ty Iso) Λ₁ Λ₂ -> (Λ : nGradedFD n ms₂ rs) -> (ty Iso) (Λ₁ ∙ Λ) (Λ₂ ∙ Λ)
ε ∙ᵗʳ Λ = ε
(emb {ms₁'} {ms₂'} {Λ₁'} {Λ₂'} p as bs Λl Λr ∷ᵗ ps) ∙ᵗʳ Λ = p' ∷ᵗ (ps  ∙ᵗʳ Λ)
  where eq : ∀ (Λᵢ : nGradedFD _ ms₁' ms₂') -> (Λl ∙ as ◅ Λᵢ ▻ bs ∙ Λr) ∙ Λ ≡ Λl ∙ as ◅ Λᵢ ▻ bs ∙ (Λr ∙ Λ)
        eq Λᵢ = trans (trans (cong (_∙ Λ) (sym (∙-assoc Λl (as ◅ Λᵢ ▻ bs) Λr)))
                             (∙-assoc (Λl ∙ as ◅ Λᵢ ▻ bs) Λr Λ))
                             (∙-assoc Λl (as ◅ Λᵢ ▻ bs) (Λr ∙ Λ))
        p' : MonoidalClosure _ ((Λl ∙ as ◅ Λ₁' ▻ bs ∙ Λr) ∙ Λ) ((Λl ∙ as ◅ Λ₂' ▻ bs ∙ Λr) ∙ Λ)
        p' rewrite eq Λ₁' | eq Λ₂' = emb p as bs Λl (Λr ∙ Λ)
infixr 5 _∙ᵗʳ_

_◅ᵗ_ : ∀ {n} {ty : IsoType n} {ms₁ ms₂} {Λ₁ Λ₂ : nGradedFD n ms₁ ms₂}
       -> (xs : nVec _) -> (ty Iso) Λ₁ Λ₂ -> (ty Iso) (xs ◅ Λ₁) (xs ◅ Λ₂)
xs ◅ᵗ ε = ε
xs ◅ᵗ (emb {ms₁'} {ms₂'} {Λ₁'} {Λ₂'} p as bs Λl Λr ∷ᵗ ps) = p' ∷ᵗ (xs ◅ᵗ ps)
  where eq : ∀ (Λᵢ : nGradedFD _ ms₁' ms₂') -> xs ◅ (Λl ∙ as ◅ Λᵢ ▻ bs ∙ Λr) ≡ (xs ◅ Λl) ∙ (xs ++* as) ◅ Λᵢ ▻ bs ∙ (xs ◅ Λr)
        eq Λᵢ =  trans (trans (◅-distrib xs Λl (as ◅ Λᵢ ▻ bs ∙ Λr))
                              (cong (xs ◅ Λl ∙_) (◅-distrib xs (as ◅ Λᵢ ▻ bs) Λr)))
                              (cong (λ z → xs ◅ Λl ∙ z ∙ xs ◅ Λr) (sym (++*-acts-on-◅ xs as (Λᵢ ▻ bs))))
        p' : MonoidalClosure _ (xs ◅ (Λl ∙ as ◅ Λ₁' ▻ bs ∙ Λr)) (xs ◅ (Λl ∙ as ◅ Λ₂' ▻ bs ∙ Λr))
        p' rewrite eq Λ₁' | eq Λ₂' = emb p (xs ++* as) bs (xs ◅ Λl) (xs ◅ Λr)
infixr 6 _◅ᵗ_

_▻ᵗ_ : ∀ {n} {ty : IsoType n} {ms₁ ms₂} {Λ₁ Λ₂ : nGradedFD n ms₁ ms₂}
        -> (ty Iso) Λ₁ Λ₂ -> (xs : nVec _) -> (ty Iso) (Λ₁ ▻ xs) (Λ₂ ▻ xs)
ε ▻ᵗ xs = ε
(emb {ms₁'} {ms₂'} {Λ₁'} {Λ₂'} p as bs Λl Λr ∷ᵗ ps) ▻ᵗ xs = p' ∷ᵗ (ps  ▻ᵗ xs)
  where eq : ∀ (Λᵢ : nGradedFD _ ms₁' ms₂') -> (Λl ∙ as ◅ Λᵢ ▻ bs ∙ Λr) ▻ xs ≡ (Λl ▻ xs) ∙ as ◅ Λᵢ ▻ (bs ++* xs) ∙ Λr ▻ xs
        eq Λᵢ =  trans (▻-distrib Λl (as ◅ Λᵢ ▻ bs ∙ Λr) xs)
                (trans (cong (Λl ▻ xs ∙_) (▻-distrib (as ◅ Λᵢ ▻ bs) Λr xs))
                (trans (cong (λ z → Λl ▻ xs ∙ z ∙ Λr ▻ xs) (sym (◅-▻-assoc-lemma as Λᵢ bs xs)))
                (trans (cong (λ z → Λl ▻ xs ∙ z ∙ Λr ▻ xs) (++*-acts-on-▻ (as ◅ Λᵢ) bs xs))
                       (cong (λ z → Λl ▻ xs ∙ z ∙ Λr ▻ xs) (◅-▻-assoc as Λᵢ (bs ++* xs))))))
        p' : MonoidalClosure _ ((Λl ∙ as ◅ Λ₁' ▻ bs ∙ Λr) ▻ xs) ((Λl ∙ as ◅ Λ₂' ▻ bs ∙ Λr) ▻ xs)
        p' rewrite eq Λ₁' | eq Λ₂' = emb p as (bs ++* xs) (Λl ▻ xs) (Λr ▻ xs)
infixl 7 _▻ᵗ_

embᵗ : ∀ {n} {ty : IsoType n} {ms₁ ms₂} {Λ₁ Λ₂ : nGradedFD n ms₁ ms₂} -> (ty Iso) Λ₁ Λ₂
       -> ∀ (as bs : nVec _)
       -> ∀ {l} (Λl : nGradedFD n l (as ++* ms₁ ++* bs)  )
            {r} (Λr : nGradedFD n   (as ++* ms₂ ++* bs) r)
       -> (ty Iso) (Λl ∙ as ◅ Λ₁ ▻ bs ∙ Λr) (Λl ∙ as ◅ Λ₂ ▻ bs ∙ Λr)
embᵗ p as bs Λl Λr = Λl ∙ᵗˡ as ◅ᵗ p ▻ᵗ bs ∙ᵗʳ Λr


-- This is indeed an equivalence relation
instance
  Iso-IsEquivalence : ∀ {n} {ty : IsoType n} {ls rs} -> IsEquivalence (_Iso {n} ty {ls} {rs})
  Iso-IsEquivalence {n} {ty} {ls} {rs}
    = record { refl = ε ; trans = _++ᵗ_
             ; sym = ReflTransClosure.reverse (symM (SymClosure.symmetric (ty Gen))) }

instance
  Iso-Setoid : ∀ {n} {ty : IsoType n} {ls rs} -> Setoid _ _
  Iso-Setoid {n} {ty} {ls} {rs} = record
    { Carrier       = nGradedFD n ls rs
    ; _≈_           = (ty Iso)
    ; isEquivalence = Iso-IsEquivalence }


module Iso-Reasoning {n} {ty : IsoType n} where

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _⟨_⟩_≅⟨_⟩_ _⟨⟩_≅⟨_⟩_ _≡⟨_⟩_
  infix  1 begin_

  ι : ∀ {ms ls} -> nGradedFD n ls ms -> nGradedFD n ls ms
  ι x = x

  data _IsRelatedTo_ {ls rs} (x y : nGradedFD n ls rs) : Set where
    relTo : (ty Iso) x y → x IsRelatedTo y
  
  begin_ : ∀ {ls rs} {x y : nGradedFD n ls rs} → x IsRelatedTo y → (ty Iso) x y
  begin relTo x∼y = x∼y

  _⟨_⟩_≅⟨_⟩_ : ∀ {ls ms₁ ms₂ rs}
             -> (Λl : nGradedFD n ls ms₁)
             -> (Λ₁ : ∀ {ls} -> nGradedFD n ls ms₁ -> nGradedFD n ls ms₂)
             -> (Λr : ∀ {ls} -> nGradedFD n ls ms₂ -> nGradedFD n ls rs)
             -> {Λ₂ : nGradedFD n ms₁ ms₂} {Λ' : nGradedFD n ls rs}
             -> (ty Iso) (Λ₁ (idPat ms₁)) Λ₂
             -> (Λl ∙ Λ₂ ∙ (Λr (idPat _))) IsRelatedTo Λ'
             -> (Λl ∙ (Λ₁ (idPat _)) ∙ (Λr (idPat _))) IsRelatedTo Λ'
  Λl ⟨ Λ₁ ⟩ Λr ≅⟨ p ⟩ relTo q = relTo ((Λl ∙ᵗˡ p ∙ᵗʳ Λr (idPat _)) ++ᵗ q)

  _⟨⟩_≅⟨_⟩_ = λ {ls} {ms} {rs} Λl → _⟨_⟩_≅⟨_⟩_ {ls} {ms} {ms} {rs} Λl ι

  _≡⟨_⟩_ : ∀ {ls rs} x {y z : nGradedFD n ls rs} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ refl ⟩ p = p
  
  _∎ : ∀ {ls rs} (x : nGradedFD n ls rs) → x IsRelatedTo x
  _∎ _ = relTo ε


-- Applying a single generator
gen : ∀ {n} {ty : IsoType n} {ls rs} {Λ₁ Λ₂ : nGradedFD n ls rs} -> (ty Gen) Λ₁ Λ₂ -> (ty Iso) Λ₁ Λ₂
gen {_} {ty} {ls} {rs} {Λ₁} {Λ₂} p = rwr (emb (inj₁ p) []* []* (idPat ls) (idPat rs)) ∷ᵗ ε
  where rwr : MonoidalClosure _ (idPat _ ∙ Λ₁) (idPat _ ∙ Λ₂) -> MonoidalClosure _ Λ₁ Λ₂
        rwr p rewrite ∙-idˡ Λ₁ | ∙-idˡ Λ₂ = p

-- Testing/Examples:

-- ex-R1 : (Legn Iso) ([] <: b+ 0 , d 0) ([] <: b+ 0 , b+ 1 , c 0 , c 0 , c 1 , d 0 , d 0)
-- ex-R1 = begin
--   [] <: b+ 0 ⟨⟩ d 0 ≅⟨ gen R1-b ▻ᵗ _ ⟩
--   [] <: b+ 0 , b+ 1 , c 0 ⟨ d 1 ⟩ d 0 ≅⟨ gen R2-d-b ▻ᵗ _ ⟩
--   [] <: b+ 0 ⟨ b+ 1 ⟩ c 0 , c 0 , c 1 , d 0 , d 0 ≅⟨ (1 ∷* []*) ◅ᵗ gen R2-b-a ⟩
--   [] <: b+ 0 , b 2 , c 1 , c 2 , c 0 , c 0 , c 1 , d 0 , d 0 ∎
--   where open Iso-Reasoning

-- ex-rr : (Legn Iso) ([] <: b+ 0 , b+ 1 , c 0 , c 0 , c 1 , d 0 , d 0) ([] <: b+ 0 , b+ 2 , c 1 , c 2 , c 0 , c 0 , c 1 , d 0 , d 0)
-- ex-rr = begin
--   [] <: b+ 0 ⟨ b+ 1 ⟩ c 0 , c 0 , c 1 , d 0 , d 0 ≅⟨ ? ⟩
--   [] <: b+ 0 , b+ 2 , c 1 , c 2 , c 0 , c 0 , c 1 , d 0 , d 0 ∎
--   where open Iso-Reasoning
