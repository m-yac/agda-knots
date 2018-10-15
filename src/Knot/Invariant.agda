

---------------------
-- Currently Broken!
---------------------


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

import Data.Integer.Properties as ℤProp
open import Function using (_∘_; _on_)






-- open import Relation.Binary.Core as Bin using (Rel; _⇒_; _=[_]⇒_; IsEquivalence)
-- open import Function using (_∘_; _on_)

-- _Invariant_wrt_ : ∀ {n} (ty : IsoType n) {a} {A : ∀ {l r} (ls : Vec (ℤmod n) l) (rs : Vec (ℤmod n) r) -> Set a}
--                   -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A ls rs)
--                   -> ∀ {ℓ} (P : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> Rel (A ls rs) ℓ)
--                        {{isEquiv : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> IsEquivalence (P {l} {r} {ls} {rs})}} -> Set _
-- ty Invariant f wrt P = ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> (ty Iso) =[ f {l} {r} {ls} {rs} ]⇒ P

-- _Pattern-Invariant_wrt_ : ∀ {n} (ty : IsoType n) {a} {A : ∀ {l} (ls : Vec (ℤmod n) l) -> Set a}
--                          -> ∀ (f : ∀ {l} {ls : Vec _ l} -> nGradedFD n ls ls -> A ls)
--                          -> ∀ {ℓ} (P : ∀ {l} {ls : Vec _ l} -> Rel (A ls) ℓ)
--                               {{isEquiv : ∀ {l} {ls : Vec _ l} -> IsEquivalence (P {l} {ls})}} -> Set _
-- ty Pattern-Invariant f wrt P = ∀ {l} {ls : Vec _ l} -> (ty Iso) =[ f {l} {ls} ]⇒ P

-- _Link-Invariant_wrt_ : ∀ {n} (ty : IsoType n) {a} {A : Set a}
--                          -> ∀ (f : nGradedFD n [] [] -> A)
--                          -> ∀ {ℓ} (P : Rel A ℓ) {{isEquiv : IsEquivalence P}} -> Set _
-- ty Link-Invariant f wrt P = (ty Iso) =[ f ]⇒ P


-- -- Proving _Invariant_wrt_ directly is inconvient... use `pv-invariant` instead!

-- -- (see `by-split-+` as a way to prove this)
-- resp-+-on_wrt_ : ∀ {n} {a} {A : ∀ {l r} (ls : Vec (ℤmod n) l) (rs : Vec (ℤmod n) r) -> Set a}
--                  -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A ls rs)
--                  -> ∀ {ℓ} (P : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> Rel (A ls rs) ℓ)
--                       {{isEquiv : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> IsEquivalence (P {l} {r} {ls} {rs})}} -> Set _
-- resp-+-on f wrt P = ∀ {l m r} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r}
--                     -> (Λl : nGradedFD _ ls ms) {Λl' : nGradedFD _ ls ms} (Λr : nGradedFD _ ms rs) {Λr' : nGradedFD _ ms rs}
--                     -> (P on f) Λl Λl' -> (P on f) Λr Λr' -> (P on f) (Λl + Λr) (Λl' + Λr')

-- -- (see `by-split-∷*` as a way to prove this)
-- resp-∷*-on_wrt_ : ∀ {n} {a} {A : ∀ {l r} (ls : Vec (ℤmod n) l) (rs : Vec (ℤmod n) r) -> Set a}
--                   -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A ls rs)
--                   -> ∀ {ℓ} (P : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> Rel (A ls rs) ℓ)
--                        {{isEquiv : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> IsEquivalence (P {l} {r} {ls} {rs})}} -> Set _
-- resp-∷*-on f wrt P = ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} (μ : ℤmod _)
--                      -> (Λ : nGradedFD _ ls rs) {Λ' : nGradedFD _ ls rs}
--                      -> (P on f) Λ Λ' -> (P on f) (μ ∷* Λ) (μ ∷* Λ')

-- -- (proofs of this should be long but wholly trivial)
-- _Gen-Invariant_wrt_ : ∀ {n} (ty : IsoType n) {a} {A : ∀ {l r} (ls : Vec (ℤmod n) l) (rs : Vec (ℤmod n) r) -> Set a}
--                       -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A ls rs)
--                       -> ∀ {ℓ} (P : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> Rel (A ls rs) ℓ)
--                            {{isEquiv : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> IsEquivalence (P {l} {r} {ls} {rs})}} -> Set _
-- ty Gen-Invariant f wrt P = ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> (ty Gen) =[ f {l} {r} {ls} {rs} ]⇒ P


-- pv-invariant : ∀ {n} {ty : IsoType n} {a} {A : ∀ {l r} (ls : Vec (ℤmod n) l) (rs : Vec (ℤmod n) r) -> Set a}
--                -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A ls rs)
--                -> ∀ {ℓ} {P : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> Rel (A ls rs) ℓ}
--                     {{isEquiv : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> IsEquivalence (P {l} {r} {ls} {rs})}}
--                -> resp-+-on f wrt P
--                -> resp-∷*-on f wrt P
--                -> ty Gen-Invariant f wrt P
--                -> ty Invariant f wrt P
-- pv-invariant {n} {ty} f {P = P} {{isEquiv = pf}} rsp-+ rsp-∷* gen-invar
--   = ReflTransClosureEq ∘ ReflTransClosure.gmap f ~invar
--   where ~invar : _~_ =[ f ]⇒ P
--         ~invar (x below ts btwn Λl , Λr)
--           = rsp-+ _ Λr (rsp-+ Λl _ (IsEquivalence.refl pf) (rsp-above ts (sym-gen-invar x)))
--                        (IsEquivalence.refl pf)
--           where sym-gen-invar : SymClosure (ty Gen) =[ f ]⇒ P
--                 sym-gen-invar (fwd x) = gen-invar x
--                 sym-gen-invar (bwd y) = IsEquivalence.sym pf (gen-invar y)
--                 rsp-above : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} {Λ₁ Λ₂ : nGradedFD _ ls rs}
--                             -> ∀ {t} (ts : Vec _ t)
--                             -> (P on f) Λ₁ Λ₂ -> (P on f) (ts ◅ Λ₁) (ts ◅ Λ₂)
--                 rsp-above [] eq = eq
--                 rsp-above (x ∷ ts) eq = rsp-∷* x _ (rsp-above ts eq)
                
--         ReflTransClosureEq : ∀ {a ℓ} {A : Set a} {P : Rel A ℓ} {{isEquiv : IsEquivalence P}} -> ReflTransClosure P ⇒ P
--         ReflTransClosureEq {{isEquiv = pf}} ε            = IsEquivalence.refl pf
--         ReflTransClosureEq {{isEquiv = pf}} (x trans xs) = IsEquivalence.trans pf x (ReflTransClosureEq xs)



-- -- In fact, proving _Invariant_wrt_ with pv-invariant is also inconvient, the following functions make it simpler:
-- -- (TBD if there are any proofs which *cannot* go through using these...)
-- -- [currently unfinished! - f not fully dependent]

-- -- (ideally just an unfolding of f)
-- _splits-+-on_ : ∀ {n} {a} {A : Set a} (_+'_ : A -> A -> A)
--                 -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A) -> Set _
-- _+'_ splits-+-on f = ∀ {l m r} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r}
--                      -> (Λl : nGradedFD _ ls ms) (Λr : nGradedFD _ ms rs)
--                      -> f(Λl + Λr) ≡ f(Λl) +' f(Λr)

-- -- (trivial for _≡_)
-- _resp-+-wrt_ : ∀ {a} {A : Set a} (_+'_ : A -> A -> A)
--                -> ∀ {ℓ} (P : Rel A ℓ) {{isEquiv : IsEquivalence P}} -> Set _
-- _+'_ resp-+-wrt P = ∀ a {a'} b {b'} -> P a a' -> P b b' -> P (a +' b) (a' +' b')


-- by-split-+ : ∀ {n} {a} {A : Set a}
--              -> ∀ {f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A}
--              -> ∀ {ℓ} {P : Rel A ℓ} {{isEquiv : IsEquivalence P}}
--              -> {_+'_ : A -> A -> A}
--              -> _+'_ splits-+-on f
--              -> _+'_ resp-+-wrt P
--              -> resp-+-on f wrt P
-- by-split-+ spl rsp Λl {Λl'} Λr {Λr'} eql eqr rewrite spl Λl Λr | spl Λl' Λr' = rsp _ _ eql eqr


-- -- (trivial for _≡_)
-- _splits-∷*-on_ : ∀ {n} {a} {A : Set a} (_∷'_ : ℤmod n -> A -> A)
--                  -> ∀ (f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A) -> Set _
-- _∷'_ splits-∷*-on f = ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} μ
--                       -> (Λ : nGradedFD _ ls rs)
--                       -> f(μ ∷* Λ) ≡ μ ∷' f(Λ)

-- -- (ideally just an unfolding of f)
-- _resp-∷*-wrt_ : ∀ {n} {a} {A : Set a} (_∷'_ : ℤmod n -> A -> A)
--                 -> ∀ {ℓ} (P : Rel A ℓ) {{isEquiv : IsEquivalence P}} -> Set _
-- _∷'_ resp-∷*-wrt P = ∀ μ b {b'} -> P b b' -> P (μ ∷' b) (μ ∷' b')


-- by-split-∷* : ∀ {n} {a} {A : Set a}
--               -> ∀ {f : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> A}
--               -> ∀ {ℓ} {P : Rel A ℓ} {{isEquiv : IsEquivalence P}}
--               -> {_∷'_ : ℤmod n -> A -> A}
--               -> _∷'_ splits-∷*-on f
--               -> _∷'_ resp-∷*-wrt P
--               -> resp-∷*-on f wrt P
-- by-split-∷* spl rsp xs Λ {Λ'} eq rewrite spl xs Λ | spl xs Λ' = rsp xs _ eq




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
