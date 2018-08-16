
module Utils where

open import Agda.Primitive as Prim public


open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _≥_; _>_; ≤-pred; _≤?_) public
open import Agda.Builtin.Unit

record HasDependent+ {a} (X : Set a) (P : X -> Set a) (A : ∀ {x y} -> P x -> P y -> Set a) : Set a where
  field _+_ : ∀ {x y z} {a : P x} {b : P y} {c : P z} -> A a b -> A b c -> A a c
        unit : ∀ {x} (a : P x) -> A a a
open HasDependent+ {{...}} public

_×_ : ∀ {a} {X : Set a} {P : X -> Set a} {A : ∀ {x y} -> P x -> P y -> Set a}
        {{_ : HasDependent+ X P A}} {x : X} {a : P x} -> ℕ -> A a a -> A a a
zero × _ = unit _
(suc n) × p = p + (n × p)

instance
  ℕ-Dep+ : HasDependent+ ⊤ (\ _ -> ⊤) (\ _ _ -> ℕ)
  ℕ-Dep+ = record { _+_ = ℕ._+_; unit = \ _ -> 0 }


open import Data.Fin as Fin using (Fin; zero; suc; pred; Fin′; #_; fromℕ; fromℕ≤; toℕ; inject; inject!; inject+; inject₁; raise) public
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst) public

inj₊₁ : {n : ℕ} {i : Fin n} -> Fin′ (suc i) -> Fin n
inj₊₁ = inject!

inj₋₁ : ∀ {n} (i : Fin n) -> Fin′ (pred i) -> Fin n
inj₋₁ zero ()
inj₋₁ (suc zero) ()
inj₋₁ (suc (suc i)) zero = zero
inj₋₁ (suc (suc i)) (suc k) = suc (inj₋₁ (suc i) k)

at : {n : ℕ} -> Fin n -> Fin (suc n)
at zero = zero
at (suc i) = suc (at i)

add : ∀ m {n} → Fin n → Fin (m + n)
add zero i = i
add (suc m) i = suc (add m i)

at_up_ : {n : ℕ} -> Fin n -> (m : ℕ) -> Fin (m + n)
at_up_ i zero = i
at_up_ i (suc m) = at (at i up m)

at_up!_ : {n : ℕ} -> Fin (1 + n) -> (m : ℕ) -> Fin (1 + (m + n))
at_up!_ {_} i zero = i
at_up!_ {n} i (suc m) = at (subst Fin (+-suc m n) (at i up m))

raise! : ∀ {n} m -> Fin (1 + n) -> Fin (1 + (m + n))
raise! {_} zero    i = i
raise! {n} (suc m) i = suc (subst Fin (+-suc m n) (raise m i))

neg : ∀ {n} -> Fin n -> Fin n
neg {.suc n} zero = fromℕ n
neg {.suc n} (suc i) = at (neg {n} i)

-- open import Data.String as Str using ()
-- open import Data.Nat.Show

open import Data.Product as Σ using (Σ-syntax) public
pattern <_,_> x y = Σ._,_ x y

open import Data.Vec public
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl) public
open import Data.Vec.Properties using (++-assoc)

insert1 : ∀ {a n} {A : Set a} -> Fin (1 + n) -> A -> Vec A n -> Vec A (1 + n)
insert1 = insert

insert2 : ∀ {a n} {A : Set a} -> Fin (1 + n) -> A Σ.× A -> Vec A n -> Vec A (2 + n)
insert2 i < x , y > xs = insert (suc i) y (insert i x xs)

insert3 : ∀ {a n} {A : Set a} -> Fin (1 + n) -> A Σ.× A Σ.× A -> Vec A n -> Vec A (3 + n)
insert3 i < x , < y , z > > xs = insert2 (suc i) < y , z > (insert i x xs)

swap2 : ∀ {n} {a} {A : Set a} -> Fin (1 + n) -> Vec A (2 + n) -> Vec A (2 + n)
swap2 zero (x ∷ y ∷ xs) = y ∷ x ∷ xs
swap2 {zero} (suc ()) _
swap2 {suc _} (suc i) (x ∷ xs) = x ∷ swap2 i xs

insert2-swap2-combn : ∀ {a n} {A : Set a} (i : Fin (1 + n)) {x y : A} (xs : Vec A n)
                     -> swap2 i (insert2 i < x , y > xs) ≡ insert2 i < y , x > xs
insert2-swap2-combn zero _ = refl
insert2-swap2-combn (suc ()) []
insert2-swap2-combn (suc i) {x} {y} (z ∷ xs)
  = cong (_∷_ z) (insert2-swap2-combn i {x} {y} xs)

insert-swap2-comm : ∀ {a n} {A : Set a} (i : Fin (1 + n)) {x : A} (xs : Vec A (2 + n))
                     -> swap2 (at i) (insert (add 2 i) x xs) ≡ insert (add 2 i) x (swap2 i xs)
insert-swap2-comm zero (_ ∷ _ ∷ _) = refl
insert-swap2-comm (suc ()) (_ ∷ _ ∷ [])
insert-swap2-comm (suc i) (x ∷ y ∷ z ∷ xs)
  = cong (_∷_ x) (insert-swap2-comm i (y ∷ z ∷ xs))

insert2-insert-comm-at : ∀ {a n} {A : Set a} (i : Fin (1 + n)) {x y z : A} (xs : Vec A n)
                         -> insert2 (at i) < x , y > (insert i z xs)
                            ≡ insert (suc (suc i)) z (insert2 i < x , y > xs)
insert2-insert-comm-at zero xs = refl
insert2-insert-comm-at (suc ()) []
insert2-insert-comm-at (suc i) (x ∷ xs)
  = cong (_∷_ x) (insert2-insert-comm-at i xs)

insert2-insert-comm-suc : ∀ {a n} {A : Set a} (i : Fin (1 + n)) {x y z : A} (xs : Vec A n)
                          -> insert2 (at i) < x , y > (insert i z xs)
                             ≡ insert2 (suc i) < y , z > (insert i x xs)
insert2-insert-comm-suc zero xs = refl
insert2-insert-comm-suc (suc ()) []
insert2-insert-comm-suc (suc i) (x ∷ xs)
  = cong (_∷_ x) (insert2-insert-comm-suc i xs)

insert-insert2-comm-at : ∀ {a n} {A : Set a} (i : Fin (1 + n)) {x y z : A} (xs : Vec A n)
                         -> insert (at i up 2) x (insert2 i < y , z > xs)
                            ≡ insert2 (suc i) < y , z > (insert i x xs)
insert-insert2-comm-at zero xs = refl
insert-insert2-comm-at (suc ()) []
insert-insert2-comm-at (suc i) (x ∷ xs)
  = cong (_∷_ x) (insert-insert2-comm-at i xs)

open import Data.Integer as ℤ using (ℤ)
open import Data.Integer.Properties as ℤProp using ()
open import Data.Nat.DivMod as DivMod using (_%_; a%n%n≡a%n) public

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (True; False; toWitness) public
open ≡-Reasoning

instance
  ℤ-Dep+ : HasDependent+ ⊤ (\ _ -> ⊤) (\ _ _ -> ℤ)
  ℤ-Dep+ = record { _+_ = ℤ._+_; unit = \ _ -> ℤ.pos 0 }


ℤmod-Rep : ℕ -> Set
ℤmod-Rep zero = ℤ
ℤmod-Rep (suc n) = ℕ

ℤmod-Cond : (n : ℕ) -> ℤmod-Rep n -> Set
ℤmod-Cond zero i = ⊤
ℤmod-Cond (suc n) i = i % suc n ≡ i

ℤmod : ℕ -> Set
ℤmod n = Σ[ i ∈ ℤmod-Rep n ] (ℤmod-Cond n i)

open import Relation.Nullary using (yes)

ℤmod-Cond-Dec : (n : ℕ) -> ℤmod-Rep n -> Set
ℤmod-Cond-Dec zero i = ⊤
ℤmod-Cond-Dec (suc n) i = True (i % suc n ℕ.≟ i)

fromRep : (n : ℕ) -> (i : ℤmod-Rep n) -> {cond : ℤmod-Cond-Dec n i} -> ℤmod n
fromRep zero    i {cond} = < i , toWitness cond >
fromRep (suc n) i {cond} = < i , toWitness cond >

syntax fromRep n i = i mod n

raisem : ∀ {n} -> ℕ -> ℤmod n -> ℤmod n
raisem {zero} i < k , tt > = < ℤ.pos i ℤ.+ k , tt >
raisem {suc n} i < k , eq > = < (i ℕ.+ k) % suc n , DivMod.a%n%n≡a%n (i ℕ.+ k) n >

open import Data.Product.Relation.Pointwise.Dependent using (Pointwise-≡⇒≡; _,_)

≡-≅-irrelevanceʳ : ∀ {l} {A₁ : Set l} {a₁ a₂ a₃ a₄ : A₁} (p : a₁ ≡ a₂) (q : a₃ ≡ a₄) → a₂ ≡ a₄ → p ≅ q
≡-≅-irrelevanceʳ refl refl refl = _≅_.refl

raisem-actson : ∀ {n} i j (k : ℤmod n) -> raisem i (raisem j k) ≡ raisem (i + j) k
raisem-actson {zero} i j < k , tt > = cong (\ z -> < z , tt >) (sym (ℤProp.+-assoc (ℤ.pos i) (ℤ.pos j) k))
raisem-actson {suc n} i j < k , eq > = Pointwise-≡⇒≡ ( lem , ≡-≅-irrelevanceʳ _ _ lem )
  where lem : Σ.proj₁ (raisem i (raisem j < k , eq >)) ≡ Σ.proj₁ (raisem (i + j) < k , eq >)
        lem = begin
          ( i      +  ((j + k) % m)     ) % m ≡⟨ DivMod.%-distribˡ-+ i ((j + k) % m) n ⟩
          ((i % m) + (((j + k) % m) % m)) % m ≡⟨ cong (λ z → ((i % m) + z) % m) (a%n%n≡a%n (j + k) n) ⟩
          ((i % m) +  ((j + k) % m)     ) % m ≡⟨ sym (DivMod.%-distribˡ-+ i (j + k) n) ⟩
          ( i      +   (j + k)          ) % m ≡⟨ cong (_% m) (sym (+-assoc i j k)) ⟩
          ((i      +   j) + k           ) % m ∎
          where m = suc n

inc : ∀ {n} -> ℤmod n -> ℤmod n
inc {zero} = Σ.map₁ ℤ.suc
inc {suc n} = raisem 1

dec : ∀ {n} -> ℤmod n -> ℤmod n
dec {zero} = Σ.map₁ ℤ.pred
dec {suc n} = raisem n

inv-inc-dec : ∀ {n} (i : ℤmod n) -> inc (dec i) ≡ i
inv-inc-dec {zero} < ℤ.pos zero , tt > = refl
inv-inc-dec {zero} < ℤ.pos (suc _) , tt > = refl
inv-inc-dec {zero} < ℤ.negsuc _ , tt > = refl
inv-inc-dec {suc n} < i , eq > = Pointwise-≡⇒≡ ( lem , ≡-≅-irrelevanceʳ _ _ lem )
  where lem : Σ.proj₁ (inc (dec < i , eq >)) ≡ i
        lem = begin
          Σ.proj₁ (raisem 1 (raisem n < i , eq >)) ≡⟨ cong Σ.proj₁ (raisem-actson 1 n < i , eq >) ⟩
          Σ.proj₁ (raisem (1 + n) < i , eq >)      ≡⟨ refl ⟩
          ((suc n) + i) % suc n                    ≡⟨ cong (_% suc n) (Data.Nat.Properties.+-comm (suc n) i) ⟩
          (i + (suc n)) % suc n                    ≡⟨ DivMod.[a+n]%n≡a%n i n ⟩
          i % suc n                                ≡⟨ eq ⟩
          i                                        ∎

inv-dec-inc : ∀ {n} (i : ℤmod n) -> dec (inc i) ≡ i
inv-dec-inc {zero} < ℤ.pos _ , tt > = refl
inv-dec-inc {zero} < ℤ.negsuc zero , tt > = refl
inv-dec-inc {zero} < ℤ.negsuc (suc _) , tt > = refl
inv-dec-inc {suc n} < i , eq > = Pointwise-≡⇒≡ ( lem , ≡-≅-irrelevanceʳ _ _ lem )
  where lem : Σ.proj₁ (dec (inc  < i , eq >)) ≡ i
        lem = begin
          Σ.proj₁ (raisem n (raisem 1 < i , eq >)) ≡⟨ cong Σ.proj₁ (raisem-actson n 1 < i , eq >) ⟩
          Σ.proj₁ (raisem (n + 1) < i , eq >)      ≡⟨ cong (\ z -> Σ.proj₁ (raisem z < i , eq >)) (+-comm n 1) ⟩
          Σ.proj₁ (raisem (1 + n) < i , eq >)      ≡⟨ refl ⟩
          ((suc n) + i) % suc n                    ≡⟨ cong (_% suc n) (Data.Nat.Properties.+-comm (suc n) i) ⟩
          (i + (suc n)) % suc n                    ≡⟨ DivMod.[a+n]%n≡a%n i n ⟩
          i % suc n                                ≡⟨ eq ⟩
          i                                        ∎





