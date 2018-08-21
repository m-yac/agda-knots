
module Knot.FrontDiagram where

open import Utils


-- The front diagram of an n-graded tangle, represented as a morse word.
data nGradedFD : ∀ (n : ℕ) {l r} -> Vec (ℤmod n) l -> Vec (ℤmod n) r -> Set where
  bGr : ∀ {n l r} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n) 
        -> nGradedFD n ls rs
        -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
  cGr : ∀ {n l r} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
        -> (i : Fin (1 + r))
        -> nGradedFD n ls rs
        -> nGradedFD n ls (swap2 i rs)
  dGr : ∀ {n l r} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n)
        -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
        -> nGradedFD n ls rs
  idPat : ∀ {n l} (ls : Vec (ℤmod n) l) -> nGradedFD n ls ls


-- A tangle has arbitrary ending strands
nGradedTangleFD : ∀ n {l r} -> Vec _ l -> Vec _ r -> Set
nGradedTangleFD n ls rs = nGradedFD n ls rs

-- A pattern has fixed ending strands
nGradedPatternFD : ∀ n {l} -> Vec _ l -> Set
nGradedPatternFD n ls = nGradedFD n ls ls

-- A link (or knot) has no ending strands
nGradedLinkFD : ∀ n -> Set
nGradedLinkFD n = nGradedFD n [] []

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

_unOri : ∀ (l : ℕ)  -> Vec (ℤmod 1) l
zero unOri = []
(suc l) unOri = 0 ∷ (l unOri)

-- A 1-grading adds no information, and thus corresponds to the unoriented case
-- Since ℕ ≅ { Vec (ℤmod 1) n : n ∈ ℕ }, we just index by ℕ
UnOriTangleFD = \ l r -> 1-GradedFD (l unOri) (r unOri)
UnOriPatternFD = \ l -> 1-GradedPatternFD (l unOri)
UnOriLinkFD = 1-GradedLinkFD



-- Notation

-- A b-event with the grading inferred
b_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n} 
     -> nGradedFD n ls rs
     -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
b_ i {μ} = bGr i μ

-- A b-event with a +oriented strand above a -oriented strand
b+_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD ls rs
      -> 2-GradedFD ls (insert2 i < 1 , 0 > rs)
b+_ i = bGr i 1

-- A b-event with a -oriented strand above a +oriented strand
b-_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD ls rs
      -> 2-GradedFD ls (insert2 i < 0 , -1 > rs)
b-_ i = bGr i 0

-- A c-event
c_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
     -> (i : Fin (1 + r))
     -> nGradedFD n ls rs
     -> nGradedFD n ls (swap2 i rs)
c_ i = cGr i

-- A d-event with the grading inferred
d_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n}
     -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
     -> nGradedFD n ls rs
d_ i {μ} = dGr i μ

_,_ : ∀ {l} {X Y : Set l} -> X -> (X -> Y) -> Y
x , f = f x
infixl 5 _,_

_<:_ : ∀ {l r n} (ls : Vec (ℤmod n) l) {rs : Vec (ℤmod n) r}
       -> (nGradedFD n ls ls -> nGradedFD n ls rs) -> nGradedFD n ls rs
_ <: f = f (idPat _)
infixl 5 _<:_


-- Allows for reuse of the odd _,_ notation, see examples below:

gr_ : ∀ {m n} -> ℤmod n -> Vec (ℤmod n) m -> Vec (ℤmod n) (suc m)
gr_ i xs = xs ∷ʳ i

o-_ : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o-_ = gr 0

o+_ : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o+_ = gr 1


-- Horizontal composition, the _+_ of tangles
hcomp : ∀ {n} {l m r} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r}
        -> nGradedFD n ls ms -> nGradedFD n ms rs -> nGradedFD n ls rs
hcomp x (bGr i μ y) = bGr i μ (hcomp x y)
hcomp x (cGr i y) = cGr i (hcomp x y)
hcomp x (dGr i μ y) = dGr i μ (hcomp x y)
hcomp x (idPat ls) = x

hcomp-assoc : ∀ {n} {a b c d} {as : Vec _ a} {bs : Vec _ b} {cs : Vec _ c} {ds : Vec _ d}
              -> (α : nGradedFD n as bs) (β : nGradedFD n bs cs) (γ : nGradedFD n cs ds)
              -> hcomp (hcomp α β) γ ≡ hcomp α (hcomp β γ)
hcomp-assoc α β (bGr i μ γ) = cong (bGr i μ) (hcomp-assoc α β γ)
hcomp-assoc α β (cGr i γ) = cong (cGr i) (hcomp-assoc α β γ)
hcomp-assoc α β (dGr i μ γ) = cong (dGr i μ) (hcomp-assoc α β γ)
hcomp-assoc α β (idPat ls) = refl

instance
  FD-Dep+ : ∀ {n} -> DependentMonoid+ ℕ (Vec (ℤmod n)) (nGradedFD n)
  FD-Dep+ = record { _+_ = hcomp; unit = idPat; identityˡ = hcomp-idˡ; identityʳ = λ _ → refl; assoc = hcomp-assoc }
    where hcomp-idˡ : ∀ {n} {l r} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs)
                      -> hcomp (idPat ls) x ≡ x
          hcomp-idˡ (bGr i μ x) = cong (bGr i μ) (hcomp-idˡ x)
          hcomp-idˡ (cGr i x) = cong (cGr i) (hcomp-idˡ x)
          hcomp-idˡ (dGr i μ x) = cong (dGr i μ) (hcomp-idˡ x)
          hcomp-idˡ (idPat ls) = refl


-- The number of events in a front diagram
len : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD n ls rs -> ℕ
len (bGr _ _ x) = suc (len x)
len (cGr _ x) = suc (len x)
len (dGr _ _ x) = suc (len x)
len (idPat _) = zero

len-hcomp : ∀ {n} {l m r} {ls : Vec _ l} {ms : Vec _ m} {rs : Vec _ r}
            -> (x : nGradedFD n ls ms) (y : nGradedFD n ms rs)
            -> len (x + y) ≡ len y + len x
len-hcomp x (bGr i μ y) = cong suc (len-hcomp x y)
len-hcomp x (cGr i y) = cong suc (len-hcomp x y)
len-hcomp x (dGr i μ y) = cong suc (len-hcomp x y)
len-hcomp x (idPat ls) = refl


-- Adding a strand with a given grading above a front diagram
_∷*_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (μt : ℤmod n)
       -> nGradedFD _ ls rs -> nGradedFD _ (μt ∷ ls) (μt ∷ rs)
μt ∷* (bGr i μ x) = bGr (suc i) μ (μt ∷* x)
μt ∷* (cGr i   x) = cGr (suc i)   (μt ∷* x)
μt ∷* (dGr i μ x) = dGr (suc i) μ (μt ∷* x)
μt ∷* (idPat ls) = idPat (μt ∷ ls)

-- Adding a arbitrary number of strands above a front diagram
_above_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {t} (ts : Vec _ t)
          -> nGradedFD n ls rs -> nGradedFD n (ts ++ ls) (ts ++ rs)
[] above x = x
(μt ∷ ts) above x = μt ∷* (ts above x)
infix 30 _above_


-- Is this no longer necessary?

-- open import Data.Product as Σ using (Σ-syntax)

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


-- Testing/Examples:

ex : TangleFD [] []
ex = dGr 0 _ (bGr 0 1 (idPat []))

ex' : TangleFD [] []
ex' = _ <: b+ 0 , d 0

ex2 : TangleFD ([] , gr 0 , gr 1) ([] , gr 1 , gr 0)
ex2 = _ <: c 0 , d 0 , b+ 0

ex3 : TangleFD [] _
ex3 = _ <: b+ 0 , c 0

ex4 : UnOriTangleFD 2 2
ex4 = _ <: c 0

unknot : LinkFD
unknot = [] <: b+ 0 , d 0

3-1a : LinkFD
3-1a = [] <: b+ 0 , b+ 1 , c 0 , c 2 , c 0 , d 1 , d 0

3-1b : LinkFD
3-1b = [] <: b+ 0 , b- 0 , c 1 , c 1 , c 1 , d 0 , d 0

m-3-1a : LinkFD
m-3-1a = [] <: b+ 0 , b- 1 , b- 3 , c 0 , c 2 , c 4 , d 3 , d 1 , d 0


