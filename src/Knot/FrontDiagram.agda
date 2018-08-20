
module Knot.FrontDiagram where

open import Utils


data nGradedFD : ∀ {l r} (n : ℕ) -> Vec (ℤmod n) l -> Vec (ℤmod n) r -> Set where
  bGr : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n) 
        -> nGradedFD n ls rs
        -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
  cGr : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
        -> (i : Fin (1 + r))
        -> nGradedFD n ls rs
        -> nGradedFD n ls (swap2 i rs)
  dGr : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
        -> (i : Fin (1 + r)) -> (μ : ℤmod n)
        -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
        -> nGradedFD n ls rs
  idPat : ∀ {l n} (ls : Vec (ℤmod n) l) -> nGradedFD n ls ls

GradedFD : ∀ {l r} -> Vec _ l -> Vec _ r -> Set
GradedFD = nGradedFD 0

1-GradedFD : ∀ {l r} -> Vec _ l -> Vec _ r -> Set
1-GradedFD = nGradedFD 1

2-GradedFD : ∀ {l r} -> Vec _ l -> Vec _ r -> Set
2-GradedFD = nGradedFD 2


bGr' : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
       -> (i : Fin (1 + r)) -> (μ : ℤmod n) 
       -> nGradedFD n ls rs
       -> nGradedFD n ls (insert2 i < inc μ , μ > rs)
bGr' i μ x = subst (\ z -> nGradedFD _ _ (insert2 _ < inc _ , z > _)) (inv-dec-inc μ) (bGr i (inc μ) x)

dGr' : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
       -> (i : Fin (1 + r)) -> (μ : ℤmod n) 
       -> nGradedFD n ls (insert2 i < inc μ , μ > rs)
       -> nGradedFD n ls rs
dGr' i μ x = dGr i (inc μ) (subst (\ z -> nGradedFD _ _ (insert2 i < inc _ , z > _)) (sym (inv-dec-inc μ)) x)



b+_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD ls rs
      -> 2-GradedFD ls (insert2 i < 1 , 0 > rs)
b+_ i = bGr i 1

b-_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
      -> (i : Fin (1 + r))
      -> 2-GradedFD ls rs
      -> 2-GradedFD ls (insert2 i < 0 , -1 > rs)
b-_ i = bGr i 0

b_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n} 
     -> nGradedFD n ls rs
     -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
b_ i {μ} = bGr i μ

c_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
     -> (i : Fin (1 + r))
     -> nGradedFD n ls rs
     -> nGradedFD n ls (swap2 i rs)
c_ i = cGr i

d_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : Fin (1 + r)) -> {μ : ℤmod n}
     -> nGradedFD n ls (insert2 i < μ , dec μ > rs)
     -> nGradedFD n ls rs
d_ i {μ} = dGr i μ

gr_ : ∀ {m n} -> ℤmod n -> Vec (ℤmod n) m -> Vec (ℤmod n) (suc m)
gr_ i xs = xs ∷ʳ i

o-_ : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o-_ = gr 0

o+_ : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o+_ = gr 1

_,_ : ∀ {l} {X Y : Set l} -> X -> (X -> Y) -> Y
x , f = f x
infixl 5 _,_

_<:_ : ∀ {l r n} (ls : Vec (ℤmod n) l) {rs : Vec (ℤmod n) r}
       -> (nGradedFD n ls ls -> nGradedFD n ls rs) -> nGradedFD n ls rs
_ <: f = f (idPat _)
infixl 5 _<:_

_unOri : ∀ (l : ℕ)  -> Vec (ℤmod 1) l
zero unOri = []
(suc l) unOri = 0 ∷ (l unOri)


TangleFD : ∀ {l r} -> Vec _ l -> Vec _ r -> Set
TangleFD = 2-GradedFD
LinkFD = TangleFD [] []
PatternFD = \ {l} ls -> TangleFD {l} ls ls

UnOriTangleFD : ℕ -> ℕ -> Set
UnOriTangleFD m n = 1-GradedFD (m unOri) (n unOri)
UnOriLinkFD = UnOriTangleFD 0 0
UnOriPatternFD = \ n -> UnOriTangleFD n n


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


_above_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} {t} (ts : Vec _ t)
          -> nGradedFD n ls rs -> nGradedFD n (ts ++ ls) (ts ++ rs)
[] above x = x
(μt ∷ ts) above x = μt-above (ts above x)
  where μt-above : ∀ {l r} {ls : Vec _ l} {rs : Vec _ r} -> nGradedFD _ ls rs -> nGradedFD _ (μt ∷ ls) (μt ∷ rs)
        μt-above (bGr i μ x) = bGr (suc i) μ (μt-above x) 
        μt-above (cGr i   x) = cGr (suc i)   (μt-above x) 
        μt-above (dGr i μ x) = dGr (suc i) μ (μt-above x) 
        μt-above (idPat ls) = idPat (μt ∷ ls)
infix 30 _above_


open import Data.Product as Σ using (Σ-syntax)

split_before_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) -> Fin (1 + len x)
                -> Σ[ m ∈ ℕ ] (Σ[ ms ∈ Vec _ m ] ((nGradedFD n ls ms) Σ.× (nGradedFD n ms rs)))
split_before_ {_} {r} {_} {_} {rs} x zero = < r , < rs , < x , idPat rs > > >
split (bGr i μ x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
                                  in < m , < ms , < xl , bGr i μ xr > > >
split (cGr i x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
                                in < m , < ms , < xl , cGr i xr > > >
split (dGr i μ x) before suc k = let < m , < ms , < xl , xr > > > = split x before k
                                  in < m , < ms , < xl , dGr i μ xr > > >
split (idPat ls) before suc ()
-- ^ This line makes me extraordinary happy!

split-before-hcomp : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) (k : Fin (1 + len x))
                     -> let < m , < ms , < xl , xr > > > = split x before k
                         in x ≡ xl + xr
split-before-hcomp x zero = refl
split-before-hcomp (bGr i μ x) (suc k) = cong (bGr i μ) (split-before-hcomp x k)
split-before-hcomp (cGr i x) (suc k) = cong (cGr i) (split-before-hcomp x k)
split-before-hcomp (dGr i μ x) (suc k) = cong (dGr i μ) (split-before-hcomp x k)
split-before-hcomp (idPat ls) (suc ())

split-before-len : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) (k : Fin (1 + len x))
                     -> let < m , < ms , < xl , xr > > > = split x before k
                         in toℕ k ≡ len xr
split-before-len x zero = refl
split-before-len (bGr i μ x) (suc k) = cong suc (split-before-len x k)
split-before-len (cGr i x) (suc k) = cong suc (split-before-len x k)
split-before-len (dGr i μ x) (suc k) = cong suc (split-before-len x k)
split-before-len (idPat ls) (suc ())

split_after_ : ∀ {l r n} {ls : Vec _ l} {rs : Vec _ r} (x : nGradedFD n ls rs) -> Fin (1 + len x)
               -> Σ[ m ∈ ℕ ] (Σ[ ms ∈ Vec _ m ] ((nGradedFD n ls ms) Σ.× (nGradedFD n ms rs)))
split x after k = split x before (neg k)


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

3-1-1 : LinkFD
3-1-1 = [] <: b+ 0 , b+ 1 , c 0 , c 2 , c 0 , d 1 , d 0

3-1-2 : LinkFD
3-1-2 = [] <: b+ 0 , b- 0 , c 1 , c 1 , c 1 , d 0 , d 0

3-1-m-1 : LinkFD
3-1-m-1 = [] <: b+ 0 , b- 1 , b- 3 , c 0 , c 2 , c 4 , d 3 , d 1 , d 0


