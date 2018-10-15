{-# OPTIONS --rewriting #-}

module Knot.FrontDiagram where

open import Knot.Prelude
import Data.NVec.Properties as nVecProp
import Data.Product as Σ


-- The front diagram of an n-graded tangle, represented as a morse word
data nGradedFD (n : ℕ) : nVec (ℤmod n) -> nVec (ℤmod n) -> Set where
  bGr : ∀ {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n) 
        -> nGradedFD n < l , ls > < r , rs >
        -> nGradedFD n < l , ls > < 2 + r , insert2 i < μ , dec μ > rs >
  cGr : ∀ {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) (2 + r)}
        -> (i : Fin (1 + r))
        -> nGradedFD n < l , ls > < 2 + r , rs >
        -> nGradedFD n < l , ls > < 2 + r , swap2 i rs >
  dGr : ∀ {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n)
        -> nGradedFD n < l , ls > < 2 + r , insert2 i < μ , dec μ > rs >
        -> nGradedFD n < l , ls > < r , rs >
  idPat : ∀ (ls : nVec (ℤmod n)) -> nGradedFD n ls ls



-- Useful Synonyms

-- A tangle has arbitrary ending strands
nGradedTangleFD : ∀ n -> nVec _ -> nVec _ -> Set
nGradedTangleFD n ls rs = nGradedFD n ls rs

-- A pattern has fixed ending strands
nGradedPatternFD : ∀ n -> nVec _ -> Set
nGradedPatternFD n ls = nGradedFD n ls ls

-- A link (or knot) has no ending strands
nGradedLinkFD : ∀ n -> Set
nGradedLinkFD n = nGradedFD n < 0 , [] > < 0 , [] >

-- Synonyms for common gradings:

GradedFD = nGradedFD 0
GradedTangleFD = nGradedTangleFD 0
GradedPatternFD = nGradedPatternFD 0
GradedLinkFD = nGradedLinkFD 0

1-GradedFD = nGradedFD 1
1-GradedTangleFD = nGradedTangleFD 1
1-GradedPatternFD = nGradedPatternFD 1
1-GradedLinkFD = nGradedLinkFD 1

2-GradedFD = nGradedFD 2
2-GradedTangleFD = nGradedTangleFD 2
2-GradedPatternFD = nGradedPatternFD 2
2-GradedLinkFD = nGradedLinkFD 2

-- Synonyms for specific gradings:

-- A 2-grading corresponds to an orientation!
-- (by default, a tangle, etc. is an *oriented* tangle, etc.)
TangleFD = 2-GradedTangleFD
PatternFD = 2-GradedPatternFD
LinkFD = 2-GradedLinkFD

_unOri : ∀ (l : ℕ)  -> nVec (ℤmod 1)
zero unOri = < 0 , [] >
(suc l) unOri = < suc (proj₁ (l unOri)) , 0 ∷ (proj₂ (l unOri)) >

-- A 1-grading adds no information, and thus corresponds to the unoriented case
-- Since ℕ ≅ nVec (ℤmod 1), we just index by ℕ
UnOriTangleFD = \ l r -> 1-GradedFD (l unOri) (r unOri)
UnOriPatternFD = \ l -> 1-GradedPatternFD (l unOri)
UnOriLinkFD = 1-GradedLinkFD



-- Notation

-- A b-event with the grading inferred
b_ : ∀ {n} {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n} 
     -> nGradedFD n < l , ls > < r , rs >
     -> nGradedFD n < l , ls > < 2 + r , insert2 i < μ , dec μ > rs >
b_ i {μ} = bGr i μ
infix 8 b_

-- A b-event with a +oriented strand above a -oriented strand
b+_ : ∀ {l} {ls : Vec (ℤmod 2) l} {r} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD < l , ls > < r , rs >
      -> 2-GradedFD < l , ls > < 2 + r , insert2 i < 1 , 0 > rs >
b+_ i = bGr i 1
infix 8 b+_

-- A b-event with a -oriented strand above a +oriented strand
b-_ : ∀ {l} {ls : Vec (ℤmod 2) l} {r} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD < l , ls > < r , rs >
      -> 2-GradedFD < l , ls > < 2 + r , insert2 i < 0 , 1 > rs >
b-_ i = bGr i 0
infix 8 b-_

-- A c-event
c_ : ∀ {n} {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) (2 + r)}
     -> (i : Fin (1 + r))
     -> nGradedFD n < l , ls > < 2 + r , rs >
     -> nGradedFD n < l , ls > < 2 + r , swap2 i rs >
c_ i = cGr i
infix 8 c_

-- A d-event with the grading inferred
d_ : ∀ {n} {l} {ls : Vec (ℤmod n) l} {r} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n}
     -> nGradedFD n < l , ls > < 2 + r , insert2 i < μ , dec μ > rs >
     -> nGradedFD n < l , ls > < r , rs >
d_ i {μ} = dGr i μ
infix 8 d_

_,_ : ∀ {l} {X Y : Set l} -> X -> (X -> Y) -> Y
x , f = f x
infixl 5 _,_

_<:_ : ∀ {n} {l} (ls : Vec (ℤmod n) l) {rs : nVec (ℤmod n)}
       -> (nGradedFD n < l , ls > < l , ls > -> nGradedFD n < l , ls > rs)
       -> nGradedFD n < l , ls > rs
_ <: f = f (idPat _)
infixl 5 _<:_

-- Allows for reuse of the odd _,_ notation, see examples below:

gr_ : ∀ {n} -> ℤmod n -> nVec (ℤmod n) -> nVec (ℤmod n)
gr_ i < n , xs > = < suc n , xs ∷ʳ i >

o-_ : nVec (ℤmod 2) -> nVec (ℤmod 2)
o-_ = gr 0

o+_ : nVec (ℤmod 2) -> nVec (ℤmod 2)
o+_ = gr 1



-- Operations

-- Concatenation/composition of tangles
_∙_ : ∀ {n} {ls ms rs} -> nGradedFD n ls ms -> nGradedFD n ms rs -> nGradedFD n ls rs
Λ₁ ∙ (bGr i μ Λ₂) = bGr i μ (Λ₁ ∙ Λ₂)
Λ₁ ∙ (cGr i   Λ₂) = cGr i   (Λ₁ ∙ Λ₂)
Λ₁ ∙ (dGr i μ Λ₂) = dGr i μ (Λ₁ ∙ Λ₂)
Λ₁ ∙ (idPat ls ) = Λ₁
infixr 5 _∙_

-- Adding a strand with a given grading above a front diagram
_◅₁_ : ∀ {n} (μt : ℤmod n) {ls rs} -> nGradedFD _ ls rs -> nGradedFD _ (μt ∷* ls) (μt ∷* rs)
μt ◅₁ (bGr i μ Λ) = bGr (suc i) μ (μt ◅₁ Λ)
μt ◅₁ (cGr i   Λ) = cGr (suc i)   (μt ◅₁ Λ)
μt ◅₁ (dGr i μ Λ) = dGr (suc i) μ (μt ◅₁ Λ)
μt ◅₁ (idPat ls) = idPat (μt ∷* ls)

-- Adding a arbitrary number of strands above a front diagram
_◅_ : ∀ {n} (ts : nVec _) {ls rs} -> nGradedFD n ls rs -> nGradedFD n (ts ++* ls) (ts ++* rs)
[]* ◅ Λ = Λ
(μt ∷*< n , μs >) ◅ Λ = μt ◅₁ (< n , μs > ◅ Λ)
infixr 6 _◅_

-- (Note: The following two definitions only work because of rewrite magic! See Knot.Prelude...)

-- Adding a strand with a given grading below a front diagram
_▻₁_ : ∀ {n} {ls rs} -> nGradedFD _ ls rs -> (μt : ℤmod n) -> nGradedFD _ (ls ∷ʳ* μt) (rs ∷ʳ* μt)
(bGr {rs = rs} i μ Λ) ▻₁ μt = bGr (at i) μ (Λ ▻₁ μt)
(cGr {rs = rs} i   Λ) ▻₁ μt = cGr (at i)   (Λ ▻₁ μt)
(dGr {rs = rs} i μ Λ) ▻₁ μt = dGr (at i) μ (Λ ▻₁ μt)
(idPat ls) ▻₁ μt = idPat (ls ∷ʳ* μt)

-- Adding a arbitrary number of strands below a front diagram
_▻_ : ∀ {n} {ls rs} -> nGradedFD n ls rs -> (ts : nVec _) -> nGradedFD n (ls ++* ts) (rs ++* ts)
Λ ▻ []* = Λ
Λ ▻ (μt ∷*< n , μs >) = (Λ ▻₁ μt) ▻ < n , μs >
infixl 7 _▻_



-- Testing/Examples:

ex : TangleFD []* []*
ex = dGr 0 _ (bGr 0 1 (idPat []*))

ex' : TangleFD []* []*
ex' = _ <: b+ 0 , d 0

ex2 : TangleFD ([]* , gr 0 , gr 1) ([]* , gr 1 , gr 0)
ex2 = _ <: c 0 , d 0 , b+ 0

ex3 : TangleFD []* _
ex3 = _ <: b+ 0 , c 0

ex4 : UnOriTangleFD 2 2
ex4 = _ <: c 0

unknot : LinkFD
unknot = _ <: b+ 0 , d 0

3-1a : LinkFD
3-1a = _ <: b+ 0 , b+ 1 , c 0 , c 2 , c 0 , d 1 , d 0

3-1b : LinkFD
3-1b = _ <: b+ 0 , b- 0 , c 1 , c 1 , c 1 , d 0 , d 0

m-3-1a : LinkFD
m-3-1a = _ <: b+ 0 , b- 1 , b- 3 , c 0 , c 2 , c 4 , d 3 , d 1 , d 0



-- Is this no longer necessary?

-- open import Data.Product as Σ using (Σ-syntax)

-- len : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> ℕ
-- len (bGr _ _ x) = suc (len x)
-- len (cGr _ x) = suc (len x)
-- len (dGr _ _ x) = suc (len x)
-- len (idPat _) = zero

-- split_before_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) -> Fin (1 + len x)
--                 -> Σ[ m ∈ ℕ ] (Σ[ ms ∈ Vec _ m ] ((nGradedFD n ls ms) Σ.× (nGradedFD n ms rs)))
-- split_before_ {_} {r} {_} {_} {rs} x zero = < r , < rs , < x , idPat rs > > >
-- split (bGr i μ x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
--                                   in < m , < ms , < xl , bGr i μ xr > > >
-- split (cGr i x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
--                                 in < m , < ms , < xl , cGr i xr > > >
-- split (dGr i μ x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
--                                   in < m , < ms , < xl , dGr i μ xr > > >
-- split (idPat ls) before suc ()
-- -- ^ This line makes me extraordinary happy!

-- split-before-hcomp : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) (k : Fin (1 + len x))
--                      -> let < m , < ms , < xl , xr > > > = split x before k
--                          in x ≡ xl + xr
-- split-before-hcomp x zero = refl
-- split-before-hcomp (bGr i μ x) (suc k) = cong (bGr i μ) (split-before-hcomp x k)
-- split-before-hcomp (cGr i x) (suc k) = cong (cGr i) (split-before-hcomp x k)
-- split-before-hcomp (dGr i μ x) (suc k) = cong (dGr i μ) (split-before-hcomp x k)
-- split-before-hcomp (idPat ls) (suc ())

-- split-before-len : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) (k : Fin (1 + len x))
--                      -> let < m , < ms , < xl , xr > > > = split x before k
--                          in toℕ k ≡ len xr
-- split-before-len x zero = refl
-- split-before-len (bGr i μ x) (suc k) = cong suc (split-before-len x k)
-- split-before-len (cGr i x) (suc k) = cong suc (split-before-len x k)
-- split-before-len (dGr i μ x) (suc k) = cong suc (split-before-len x k)
-- split-before-len (idPat ls) (suc ())

-- split_after_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) -> Fin (1 + len x)
--                -> Σ[ m ∈ ℕ ] (Σ[ ms ∈ Vec _ m ] ((nGradedFD n ls ms) Σ.× (nGradedFD n ms rs)))
-- split x after k = split x before (neg k)
