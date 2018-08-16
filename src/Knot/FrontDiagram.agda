
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


b_gr_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : ℕ) {ineq₁ : True (suc i ≤? suc r)} (μ : ℤmod-Rep n) {ineq₂ : ℤmod-Cond-Dec n μ}
     -> nGradedFD n ls rs
     -> nGradedFD n ls (insert2 (fromℕ≤ (toWitness ineq₁)) < (fromRep _ μ {ineq₂}) , dec (fromRep _ μ {ineq₂}) > rs)
b_gr_ i {ineq₁} μ {ineq₂} = bGr (fromℕ≤ (toWitness ineq₁)) (fromRep _ μ {ineq₂})

b+_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
     -> (i : ℕ) {ineq : True (suc i ≤? suc r)}
     -> 2-GradedFD ls rs
     -> 2-GradedFD ls (insert2 (fromℕ≤ (toWitness ineq)) < 1 mod 2 , 0 mod 2 > rs)
b+_ i {ineq} = bGr (fromℕ≤ (toWitness ineq)) (1 mod 2)

b-_ : ∀ {l r} {ls : Vec (ℤmod 2) l} {rs : Vec (ℤmod 2) r}
     -> (i : ℕ) {ineq : True (suc i ≤? suc r)}
     -> 2-GradedFD ls rs
     -> 2-GradedFD ls (insert2 (fromℕ≤ (toWitness ineq)) < 0 mod 2 , 1 mod 2 > rs)
b-_ i {ineq} = bGr (fromℕ≤ (toWitness ineq)) (0 mod 2)

b_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : ℕ) {ineq : True (suc i ≤? suc r)} {μ : ℤmod n}
     -> nGradedFD n ls rs
     -> nGradedFD n ls (insert2 (fromℕ≤ (toWitness ineq)) < μ , dec μ > rs)
b_ i {ineq} {μ} = bGr (fromℕ≤ (toWitness ineq)) μ

c_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) (2 + r)}
     -> (i : ℕ) {ineq : True (suc i ≤? suc r)}
     -> nGradedFD n ls rs
     -> nGradedFD n ls (swap2 (fromℕ≤ (toWitness ineq)) rs)
c_ i {ineq} = cGr (fromℕ≤ (toWitness ineq))

d_ : ∀ {l r n} {ls : Vec (ℤmod n) l} {rs : Vec (ℤmod n) r}
     -> (i : ℕ) {ineq : True (suc i ≤? suc r)} {μ : ℤmod n}
     -> nGradedFD n ls (insert2 (fromℕ≤ (toWitness ineq)) < μ , dec μ > rs)
     -> nGradedFD n ls rs
d_ i {ineq} {μ} = dGr (fromℕ≤ (toWitness ineq)) μ

o+ : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o+ xs = (1 mod 2) ∷ xs

o- : ∀ {m} -> Vec (ℤmod 2) m -> Vec (ℤmod 2) (suc m)
o- xs = (0 mod 2) ∷ xs

_,_ : ∀ {l} {X Y : Set l} -> X -> (X -> Y) -> Y
x , f = f x
infixl 5 _,_

_<:_ : ∀ {l r n} (ls : Vec (ℤmod n) l) {rs : Vec (ℤmod n) r}
       -> (nGradedFD n ls ls -> nGradedFD n ls rs) -> nGradedFD n ls rs
_ <: f = f (idPat _)
infixl 5 _<:_

_unOri : ∀ (l : ℕ)  -> Vec (ℤmod 1) l
zero unOri = []
(suc l) unOri = (0 mod 1) ∷ (l unOri)


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

instance
  FD-Dep+ : ∀ {n} -> HasDependent+ ℕ (Vec (ℤmod n)) (nGradedFD n)
  FD-Dep+ = record { _+_ = hcomp; unit = idPat }


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
ex = dGr (# 0) _ (bGr (# 0) (1 mod 2) (idPat []))

ex' : TangleFD [] []
ex' = _ <: b 0 gr 1 , d 0

ex2 : TangleFD ([] , o+ , o+) ([] , o+ , o+)
ex2 = _ <: c 0

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


