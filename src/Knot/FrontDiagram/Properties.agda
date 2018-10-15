{-# OPTIONS --rewriting #-}

open import Data.Nat using (ℕ)

module Knot.FrontDiagram.Properties {n : ℕ} where

open import Knot.Prelude
open import Knot.FrontDiagram
open import Data.NVec.Properties using (++-[]-isMonoid)

open import Category.Monoidal
open import Category.Monoidal.Structure
open import Relation.Binary.Dependent

open Heterogenous (nVec (ℤmod n)) (_≡_ {A = nVec (ℤmod n)}) (nGradedFD n) (_≡_ on-≡) public
open HeterogenousEquivalenceOn {{≡-IsEquivalence}} {{Equiv-on-≡ {{≡-IsPointwiseEquivalence}}}} public

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning


-- ∙ is associative

∙-assoc : ∀ {as bs cs ds} (α : nGradedFD n as bs) (β : nGradedFD n bs cs) (γ : nGradedFD n cs ds)
              -> (α ∙ β) ∙ γ ≡ α ∙ (β ∙ γ)
∙-assoc α β (bGr i μ γ) = cong (bGr i μ) (∙-assoc α β γ)
∙-assoc α β (cGr i   γ) = cong (cGr i  ) (∙-assoc α β γ)
∙-assoc α β (dGr i μ γ) = cong (dGr i μ) (∙-assoc α β γ)
∙-assoc α β (idPat _) = refl


-- ∙ has a left and right identity

∙-idˡ : ∀ {ls rs} (x : nGradedFD n ls rs) -> (idPat _) ∙ x ≡ x
∙-idˡ (bGr i μ x) = cong (bGr i μ) (∙-idˡ x)
∙-idˡ (cGr i x  ) = cong (cGr i  ) (∙-idˡ x)
∙-idˡ (dGr i μ x) = cong (dGr i μ) (∙-idˡ x)
∙-idˡ (idPat ls) = refl

∙-idʳ : ∀ {ls rs} (x : nGradedFD n ls rs) -> x ∙ (idPat _) ≡ x
∙-idʳ x = refl


-- ◅₁/◅ and ▻₁/▻ associate with one another 

◅₁-▻₁-assoc : ∀ l {ms₁ ms₂} (x : nGradedFD n ms₁ ms₂) r -> ((l ◅₁ x) ▻₁ r) ≡ (l ◅₁ (x ▻₁ r))
◅₁-▻₁-assoc l (bGr i μ x) r = cong (bGr (suc (at i)) μ) (◅₁-▻₁-assoc l x r)
◅₁-▻₁-assoc l (cGr i   x) r = cong (cGr (suc (at i))  ) (◅₁-▻₁-assoc l x r)
◅₁-▻₁-assoc l (dGr i μ x) r = cong (dGr (suc (at i)) μ) (◅₁-▻₁-assoc l x r)
◅₁-▻₁-assoc l (idPat ls ) r = refl

◅₁-▻-assoc : ∀ l {ms₁ ms₂} (x : nGradedFD n ms₁ ms₂) rs -> ((l ◅₁ x) ▻ rs) ≡ (l ◅₁ (x ▻ rs))
◅₁-▻-assoc l x []* = refl
◅₁-▻-assoc l x (r ∷*< n , rs >)
  = trans (cong (_▻ < n , rs >) (◅₁-▻₁-assoc l x r))
          (◅₁-▻-assoc l (x ▻₁ r) < n , rs >) 

◅-▻₁-assoc : ∀ ls {ms₁ ms₂} (x : nGradedFD n ms₁ ms₂) r -> ((ls ◅ x) ▻₁ r) ≡ (ls ◅ (x ▻₁ r))
◅-▻₁-assoc []* x r = refl
◅-▻₁-assoc (l ∷*< n , ls >) x r
  = trans (◅₁-▻₁-assoc l (< n , ls > ◅ x) r)
          (cong (l ◅₁_) (◅-▻₁-assoc < n , ls > x r))

◅-▻-assoc : ∀ ls {ms₁ ms₂} (x : nGradedFD n ms₁ ms₂) rs -> ((ls ◅ x) ▻ rs) ≡ (ls ◅ (x ▻ rs))
◅-▻-assoc []* x rs = refl
◅-▻-assoc (l ∷*< m , ls >) x rs
  = trans (◅₁-▻-assoc l (< m , ls > ◅ x) rs)
          (cong (l ◅₁_) (◅-▻-assoc < m , ls > x rs))

◅-▻-assoc-lemma : ∀ ls {ms₁ ms₂} (x : nGradedFD n ms₁ ms₂) rs xs -> ((ls ◅ x) ▻ rs) ▻ xs ≡ (ls ◅ (x ▻ rs)) ▻ xs
◅-▻-assoc-lemma ls x rs xs rewrite ◅-▻-assoc ls x rs = refl


-- []* is the left (resp. right) identity of ◅ (and ▻)

◅-identity : ∀ {as bs} (x : nGradedFD n as bs) -> []* ◅ x ≡ x
◅-identity x = refl

▻-identity : ∀ {as bs} (x : nGradedFD n as bs) -> x ▻ []* ≡ x
▻-identity x = refl

-- ◅ and ▻ define (nVec (ℤmod n), ++*) monoid actions

++*-acts-on-◅ : ∀ as bs {cs ds} (x : nGradedFD n cs ds) -> ((as ++* bs) ◅ x) ≡ (as ◅ (bs ◅ x))
++*-acts-on-◅ []* bs x = refl
++*-acts-on-◅ (a ∷*< n , as >) bs x = cong (a ◅₁_) (++*-acts-on-◅ < n , as > bs x)

++*-acts-on-▻ : ∀ {as bs} (x : nGradedFD n as bs) cs ds -> ((x ▻ cs) ▻ ds) ≡ (x ▻ (cs ++* ds))
++*-acts-on-▻ x []* ds = refl
++*-acts-on-▻ x (c ∷*< n , cs >) ds = ++*-acts-on-▻ (x ▻₁ c) < n , cs > ds


-- ◅ and ▻ commute with idPat/++*

◅-idPat : ∀ (as bs : nVec (ℤmod n)) -> as ◅ idPat bs ≡ idPat (as ++* bs)
◅-idPat []* bs = refl
◅-idPat (a ∷*< n , as >) bs = cong (a ◅₁_) (◅-idPat < n , as > bs)

▻-idPat : ∀ (as bs : nVec (ℤmod n)) -> idPat as ▻ bs ≡ idPat (as ++* bs)
▻-idPat as []* = refl
▻-idPat as (b ∷*< n , bs >) = ▻-idPat (as ∷ʳ* b) < n , bs >


-- ◅₁/◅ and ▻₁/▻ distribute over ∙

◅₁-distrib : ∀ μ {ls ms rs} (x : nGradedFD n ls ms) (y : nGradedFD n ms rs)
             -> (μ ◅₁ (x ∙ y)) ≡ (μ ◅₁ x) ∙ (μ ◅₁ y)
◅₁-distrib μ x (bGr i μ₁ y) = cong (bGr (suc i) μ₁) (◅₁-distrib μ x y)
◅₁-distrib μ x (cGr i y   ) = cong (cGr (suc i)   ) (◅₁-distrib μ x y)
◅₁-distrib μ x (dGr i μ₁ y) = cong (dGr (suc i) μ₁) (◅₁-distrib μ x y)
◅₁-distrib μ x (idPat ls) = refl

◅-distrib : ∀ xs {ls ms rs} (x : nGradedFD n ls ms) (y : nGradedFD n ms rs)
            -> (xs ◅ (x ∙ y)) ≡ (xs ◅ x) ∙ (xs ◅ y)
◅-distrib []* x y = refl
◅-distrib (μ ∷*< n , xs >) x y = trans (cong (μ ◅₁_) (◅-distrib < n , xs > x y))
                                       (◅₁-distrib μ (< n , xs > ◅ x) (< n , xs > ◅ y))

▻₁-distrib : ∀ {ls ms rs} (x : nGradedFD n ls ms) (y : nGradedFD n ms rs) μ
             -> ((x ∙ y) ▻₁ μ) ≡ (x ▻₁ μ) ∙ (y ▻₁ μ)
▻₁-distrib x (bGr i μ₁ y) μ = cong (bGr (at i) μ₁) (▻₁-distrib x y μ)
▻₁-distrib x (cGr i y   ) μ = cong (cGr (at i)   ) (▻₁-distrib x y μ)
▻₁-distrib x (dGr i μ₁ y) μ = cong (dGr (at i) μ₁) (▻₁-distrib x y μ)
▻₁-distrib x (idPat ls) μ = refl

▻-distrib : ∀ {ls ms rs} (x : nGradedFD n ls ms) (y : nGradedFD n ms rs) xs
            -> ((x ∙ y) ▻ xs) ≡ (x ▻ xs) ∙ (y ▻ xs)
▻-distrib x y []* = refl
▻-distrib x y (μ ∷*< n , xs >) = trans (cong (_▻ < n , xs >) (▻₁-distrib x y μ))
                                       (▻-distrib (x ▻₁ μ) (y ▻₁ μ) < n , xs >)


-- All together, this makes nGradedFD n into a pre-monoidal category

FD-IsPreMonoidal : IsPreMonoidalCategory _≡_ (_≡_ on-≡) _++*_ []* (_∙_ {n}) idPat _◅_ _▻_
FD-IsPreMonoidal = record
  { ∘-isMonoid = ++-[]-isMonoid
  ; isEquivOn = Equiv-on-≡ {{≡-IsPointwiseEquivalence}}
  ; B-cong = B-cong
  ; Id-cong = cong₀-on-≡ idPat λ _ → refl
  ; ∙-cong = cong₂-on-≡ _∙_ (Eq.cong₂ _∙_)
  ; 2-assoc = λ x y z -> ≡-to-≈ (∙-assoc x y z)
  ; 2-identityˡ = λ x → ≡-to-≈ (∙-idˡ x)
  ; 2-identityʳ = λ x → ≡-to-≈ (∙-idʳ x)
  ; wsk-congˡ = wsk-congˡ
  ; wsk-congʳ = wsk-congʳ
  ; wsk-assoc = λ x y z → ≡-to-≈ (◅-▻-assoc x y z)
  ; wsk-identityˡ = λ x → ≡-to-≈ (◅-identity x)
  ; wsk-identityʳ = λ x → ≡-to-≈ (▻-identity x)
  ; ∘-acts-on-wskˡ = λ x y z → ≡-to-≈ (++*-acts-on-◅ x y z)
  ; ∘-acts-on-wskʳ = λ x y z → ≡-to-≈ (++*-acts-on-▻ x y z)
  ; wsk-2-identityˡ = λ a b → ≡-to-≈ (◅-idPat a b)
  ; wsk-2-identityʳ = λ a b → ≡-to-≈ (▻-idPat a b)
  ; wsk-distribˡ = λ x y z → ≡-to-≈ (◅-distrib x y z)
  ; wsk-distribʳ = λ x y z → ≡-to-≈ (▻-distrib x y z)
  } where B-cong : ∀ {a a' b b'} -> a ≡ a' -> b ≡ b' -> nGradedFD n a b -> nGradedFD n a' b'
          B-cong refl refl x = x
          wsk-congˡ : ∀ {a a' b b' c c'} {x : nGradedFD n b c} {y : nGradedFD n b' c'}
                      -> a ≡ a' -> x ≈ y -> a ◅ x ≈ a' ◅ y
          wsk-congˡ refl < refl , < refl , refl > > = refl-on
          wsk-congʳ : ∀ {a a' b b' c c'} {x : nGradedFD n a b} {y : nGradedFD n a' b'}
                      -> c ≡ c' -> x ≈ y -> x ▻ c ≈ y ▻ c'
          wsk-congʳ refl < refl , < refl , refl > > = refl-on

instance
  FD-PreMonoidal : PreMonoidalCategory _ _ _ _
  FD-PreMonoidal = record { isPreMonoidalCategory = FD-IsPreMonoidal }
