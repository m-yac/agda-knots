
module LegKnots where

open import Utils
open import FrontDiagrams




inj : {n : ℕ} {i : Fin (suc n)} -> Fin′ (suc i) -> Fin (suc n)
inj = inject!

at : {n : ℕ} -> Fin n -> Fin (suc n)
at zero = zero
at (suc i) = suc (at i)

add : ∀ m {n} → Fin n → Fin (m + n)
add zero i = i
add (suc m) i = suc (add m i)

at_up_ : {n : ℕ} -> Fin n -> (m : ℕ) -> Fin (m + n)
at_up_ i zero = i
at_up_ i (suc m) = at (at i up m)

data RMove : {m n : ℕ} -> LegFD m n -> LegFD m n -> Set where
  ----------------
  -- R0 moves, between each possible pairing of the events
  -- Notation: "R0-x-b i j" starts with 'x i' to the below-left of 'b j'
  --           "R0-x-c i j" starts with 'x (2+i)' to the below-left of 'c j'
  --           "R0-x-d i j" starts with 'x (2+i)' to the below-left of 'd j'
  R0-b-b : {m n : ℕ} {Λ : LegFD m n      } (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , bCons i       , bCons (at (inj j) up 2))
                 (Λ , bCons (inj j) , bCons (add 2 i)        )
  R0-b-c : {m n : ℕ} {Λ : LegFD m (2 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , bCons (add 2 i) , cCons (at (inj j) up 2))
                 (Λ , cCons (inj j)   , bCons (add 2 i)        )
  R0-b-d : {m n : ℕ} {Λ : LegFD m (2 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , bCons (add 2 i) , dCons (at (inj j) up 2))
                 (Λ , dCons (inj j)   , bCons i                )
  R0-c-b : {m n : ℕ} {Λ : LegFD m (2 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , cCons i                 , bCons (at (inj j) up 2))
                 (Λ , bCons (at (inj j) up 2) , cCons (add 2 i)        )
  R0-c-c : {m n : ℕ} {Λ : LegFD m (4 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , cCons (add 2 i)         , cCons (at (inj j) up 2))
                 (Λ , cCons (at (inj j) up 2) , cCons (add 2 i)        )
  R0-c-d : {m n : ℕ} {Λ : LegFD m (4 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , cCons (add 2 i)         , dCons (add 2 (inj j)))
                 (Λ , dCons (at (inj j) up 2) , cCons i              )
  R0-d-b : {m n : ℕ} {Λ : LegFD m (2 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , dCons i                 , bCons (inj j))
                 (Λ , bCons (at (inj j) up 2) , dCons (add 2 i)        )
  R0-d-c : {m n : ℕ} {Λ : LegFD m (4 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , dCons (add 2 i)         , cCons (inj j)  )
                 (Λ , cCons (at (inj j) up 2) , dCons (add 2 i))
  R0-d-d : {m n : ℕ} {Λ : LegFD m (4 + n)} (i : Fin (suc n)) (j : Fin′ (suc i)) ->
           RMove (Λ , dCons (add 2 i)         , dCons (inj j))
                 (Λ , dCons (at (inj j) up 2) , dCons i      )
  ----------------
  -- R1 moves, both Above and Below
  R1-a : {m n : ℕ} {Λ : LegFD m (1 + n)} (i : Fin (suc n)) ->
         RMove (Λ , bCons (at i)  , cCons (suc i) , dCons (at i) ) Λ
  R1-b : {m n : ℕ} {Λ : LegFD m (1 + n)} (i : Fin (suc n)) ->
         RMove (Λ , bCons (suc i) , cCons (at i)  , dCons (suc i)) Λ
  ----------------
  -- R2 moves, in the SW, NW, SE, and NE directions
  R2-sw : {m n : ℕ} {Λ : LegFD m (1 + n)} (i : Fin (suc n)) ->
          RMove (Λ , bCons (at i))
                (Λ , bCons (suc i) , cCons (at i) , cCons (suc i))
  R2-nw : {m n : ℕ} {Λ : LegFD m (1 + n)} (i : Fin (suc n)) ->
          RMove (Λ , bCons (suc i))
                (Λ , bCons (at i) , cCons (suc i) , cCons (at i))
  R2-se : {m n : ℕ} {Λ : LegFD m (3 + n)} (i : Fin (suc n)) ->
          RMove (Λ , dCons (at i))
                (Λ , cCons (suc i) , cCons (at i) , dCons (suc i))
  R2-ne : {m n : ℕ} {Λ : LegFD m (3 + n)} (i : Fin (suc n)) ->
          RMove (Λ , dCons (suc i))
                (Λ , cCons (at i) , cCons (suc i) , dCons (at i))
  ----------------
  -- R3 moves, with the strand both in Front and Behind
  R3-f : {m n : ℕ} {Λ : LegFD m (3 + n)} (i : Fin (suc n)) ->
         RMove (Λ , cCons (at i) , cCons (suc i) , cCons (at i))
               (Λ , cCons (suc i) , cCons (at i) , cCons (suc i))
  R3-b : {m n : ℕ} {Λ : LegFD m (3 + n)} (i : Fin (suc n)) ->
         RMove (Λ , cCons (suc i) , cCons (at i) , cCons (suc i))
               (Λ , cCons (at i) , cCons (suc i) , cCons (at i))

data LegIso : {m n : ℕ} -> LegFD m n -> LegFD m n -> Set where
  _before_    : {m n k : ℕ} {Λ₁ Λ₂ : LegFD m n} -> RMove Λ₁ Λ₂ -> (Λ′ : LegFD n k) -> LegIso (Λ₁ + Λ′) (Λ₂ + Λ′)
  inv_before_ : {m n k : ℕ} {Λ₁ Λ₂ : LegFD m n} -> RMove Λ₂ Λ₁ -> (Λ′ : LegFD n k) -> LegIso (Λ₁ + Λ′) (Λ₂ + Λ′)
  _then_ : {m n : ℕ} {Λ₁ Λ₂ Λ₃ : LegFD m n} -> LegIso Λ₁ Λ₂ -> LegIso Λ₂ Λ₃ -> LegIso Λ₁ Λ₃
  Rrefl : {m n : ℕ} {Λ : LegFD m n} -> LegIso Λ Λ

infixl 6 _then_ 

_atEnd    : {m n : ℕ} {Λ₁ Λ₂ : LegFD m n} -> RMove Λ₁ Λ₂ -> LegIso Λ₁ Λ₂
_atEnd    {m} {n} x = x before (idPat n)
inv_atEnd : {m n : ℕ} {Λ₁ Λ₂ : LegFD m n} -> RMove Λ₂ Λ₁ -> LegIso Λ₁ Λ₂
inv_atEnd {m} {n} x = inv x before (idPat n)


ex-R1 : LegIso (0 <: b 0 , d 0) (0 <: b 0 , b 0 , c 1 , d 0 , d 0)
ex-R1 = Rrefl then inv (R1-a (# 0)) before (2 <: d 0)

ex-R1' : LegIso (0 <: b 0 , d  0) (0 <: b 0 , b 2 , c 1 , c 1 , c 0 , d 1 , d 0)
ex-R1' = ex-R1 then (R0-b-b (# 0) (# 0)) before (4 <: c 1 , d 0 , d 0)
               then (R2-se (# 0)) before (2 <: d 0)


invariantUnOri : ∀ {m n} {a} {X : Set a} (P : LegFD m n -> X) -> Set a
invariantUnOri P = ∀ Λ₁ Λ₂ -> RMove Λ₁ Λ₂ -> P Λ₁ ≡ P Λ₂


open import Data.Vec
open import Data.Product as Σ using (∃-syntax)
pattern <_,_> x y = Σ._,_ x y
open import Data.Bool
open import Data.Unit
open import Data.Empty

swap : ∀ {a} {n : ℕ} {A : Set a} → Fin n → Vec A (1 + n) → Vec A (1 + n)
swap zero (x ∷ y ∷ xs) = y ∷ x ∷ xs
swap (suc n) (x ∷ xs) = x ∷ (swap n xs)

remove2 : ∀ {a} {n : ℕ} {A : Set a} → Fin (1 + n) → Vec A (2 + n) → Vec A n
remove2 zero     (_ ∷ _ ∷ xs)     = xs
remove2 (suc ()) (x ∷ y ∷ [])
remove2 (suc i)  (x ∷ y ∷ z ∷ xs) = x ∷ remove2 i (y ∷ z ∷ xs)


data Ori : Set where
  o+ : Ori
  o- : Ori

neg : Ori -> Ori
neg o+ = o-
neg o- = o+

_mul_ : Ori -> Ori -> Ori
o+ mul o+ = o+
o- mul o- = o+
_  mul _  = o-

_oeq_ : Ori -> Ori -> Bool
o+ oeq o+ = true
o- oeq o- = true
_ oeq _ = false


lcusps : ∀ {m n} -> LegFD m n -> ℕ
lcusps (bCons _ Λ) = suc (lcusps Λ)
lcusps (cCons _ Λ) = lcusps Λ
lcusps (dCons _ Λ) = lcusps Λ
lcusps (idPat _) = zero

rcusps : ∀ {m n} -> LegFD m n -> ℕ
rcusps (bCons _ Λ) = rcusps Λ
rcusps (cCons _ Λ) = rcusps Λ
rcusps (dCons _ Λ) = suc (rcusps Λ)
rcusps (idPat _) = zero

Orientation : ∀ {m n} -> LegFD m n -> Set
Orientation {m} {n} Λ = Vec Ori m Σ.× Vec Ori (lcusps Λ)


bPerm : ∀ {n} -> Fin (1 + n) -> Ori -> Vec Ori n -> Vec Ori (2 + n)
bPerm zero o xs = neg o ∷ o ∷ xs
bPerm (suc ()) _ []
bPerm (suc i) o (x ∷ xs) =  x ∷ bPerm i o xs


cPerm2 : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Vec Ori (2 + n) Σ.× Ori
cPerm2 zero (x ∷ y ∷ xs) = < y ∷ x ∷ xs , x mul y >
cPerm2 (suc ()) (_ ∷ _ ∷ [])
cPerm2 (suc i) (x ∷ y ∷ z ∷ xs) = let < xs' , o > = cPerm2 i (y ∷ z ∷ xs) in < x ∷ xs' , o >

cPerm : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Vec Ori (2 + n)
cPerm i xs = Σ.proj₁ (cPerm2 i xs)

cOri : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Ori
cOri i xs = Σ.proj₂ (cPerm2 i xs)


dPerm2 : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Vec Ori n Σ.× (Ori Σ.× Bool)
dPerm2 zero (x ∷ y ∷ xs) = < xs , < x , x oeq (neg y) > >
dPerm2 (suc ()) (_ ∷ _ ∷ [])
dPerm2 (suc i) (x ∷ y ∷ z ∷ xs) = let < xs' , ob > = dPerm2 i (y ∷ z ∷ xs) in < x ∷ xs' , ob >

dPerm : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Vec Ori n
dPerm i xs = Σ.proj₁ (dPerm2 i xs)

dOri : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Ori
dOri i xs = Σ.proj₁ (Σ.proj₂ (dPerm2 i xs))

dPermValid : ∀ {n} -> Fin (1 + n) -> Vec Ori (2 + n) -> Bool
dPermValid i xs = Σ.proj₂ (Σ.proj₂ (dPerm2 i xs))


_hasOri2_ : ∀ {m n} -> (Λ : LegFD m n) -> Orientation Λ -> (Vec Ori n) Σ.× (Vec Bool (rcusps Λ))
(bCons i Λ) hasOri2 < ol , o ∷ os > = let < os' , b > = Λ hasOri2 < ol , os >
                                       in < bPerm i o os' , b >
(cCons i Λ) hasOri2 < ol , os > = let < os' , b > = Λ hasOri2 < ol , os >
                                   in < cPerm i os' , b >
(dCons i Λ) hasOri2 < ol , os > = let < os' , b > = Λ hasOri2 < ol , os >
                                   in < dPerm i os' , dPermValid i os' ∷ b >
(idPat n) hasOri2 < ol , [] > = < ol , [] >

_hasOri_ : ∀ {m n} -> (Λ : LegFD m n) -> Orientation Λ -> Set
Λ hasOri ori = foldr _ Σ._×_ ⊤ (map T (Σ.proj₂ (Λ hasOri2 ori)))





record OriLegFD (m n : ℕ) : Set where
  constructor _withOri_pf_
  field Λ : LegFD m n
        ori : Orientation Λ
        bs : Λ hasOri ori

ex-1 : OriLegFD 0 0
ex-1 = (0 <: b 0 , d 0) withOri < [] , (o+ ∷ []) > pf _



open import Data.Integer as ℤ using (ℤ)

r : ∀ {m n} -> OriLegFD m n -> ℤ
r (bCons i Λ withOri < ol , o+ ∷ os > pf bs) = ℤ.suc (r (Λ withOri < ol , os > pf bs))
r (bCons i Λ withOri < ol , o- ∷ os > pf bs) = ℤ.pred (r (Λ withOri < ol , os > pf bs))
r (cCons i Λ withOri < ol , os > pf bs) = r (Λ withOri < ol , os > pf bs)
r (dCons i Λ withOri < ol , os > pf < _ , bs >) with dOri i (Σ.proj₁ (Λ hasOri2 < ol , os >))
...                                                | o+ = ℤ.suc (r (Λ withOri < ol , os > pf bs))
...                                                | o- = ℤ.pred (r (Λ withOri < ol , os > pf bs))
r (idPat n withOri _ pf _) = ℤ.pos 0

