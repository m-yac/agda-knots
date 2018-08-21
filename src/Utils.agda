
module Utils where

open import Agda.Primitive as Prim using () public
open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg
open import Agda.Builtin.Unit
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _≥_; _>_; ≤-pred; _≤?_) public

instance
  NumNat : Number ℕ
  NumNat .Number.Constraint _ = ⊤
  NumNat .Number.fromNat n = n

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst) public

record DependentMonoid+ {a} (X : Set a) (P : X -> Set a) (A : ∀ {x y} -> P x -> P y -> Set a) : Set a where
  field _+_ : ∀ {x y z} {a : P x} {b : P y} {c : P z} -> A a b -> A b c -> A a c
        unit : ∀ {x} (a : P x) -> A a a
        identityˡ  : ∀ {x y} {a : P x} {b : P y} (α : A a b) -> unit a + α ≡ α
        identityʳ : ∀ {x y} {a : P x} {b : P y} (α : A a b) -> α + unit b ≡ α
        assoc : ∀ {x y z w} {a : P x} {b : P y} {c : P z} {d : P w} -> (α : A a b) (β : A b c) (γ : A c d) -> (α + β) + γ ≡ α + (β + γ)
  infixl 20 _+_
open DependentMonoid+ {{...}} public

_×_ : ∀ {a} {X : Set a} {P : X -> Set a} {A : ∀ {x y} -> P x -> P y -> Set a}
        {{_ : DependentMonoid+ X P A}} {x : X} {a : P x} -> ℕ -> A a a -> A a a
zero × _ = unit _
(suc n) × p = p + (n × p)

open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; +-identityˡ; +-identityʳ)

instance
  ℕ-Dep+ : DependentMonoid+ ⊤ (\ _ -> ⊤) (\ _ _ -> ℕ)
  ℕ-Dep+ = record { _+_ = ℕ._+_; unit = \ _ -> 0; identityˡ = +-identityˡ; identityʳ = +-identityʳ; assoc = +-assoc}


open import Data.Fin as Fin using (Fin; zero; suc; pred; Fin′; fromℕ; fromℕ≤; toℕ; inject; inject!; inject+; inject₁; raise) public
open import Relation.Nullary.Decidable using (True; False; toWitness) public

instance
  NumFin : ∀ {n} -> Number (Fin n)
  NumFin {n} .Number.Constraint m = True (suc m ℕ.≤? n)
  NumFin {n} .Number.fromNat m {{m≤n}} = fromℕ≤ {m} {n} (toWitness m≤n)

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
open ≡-Reasoning

open import Data.Product.Relation.Pointwise.Dependent using (Pointwise-≡⇒≡; _,_)
≡-≅-irrelevanceʳ : ∀ {l} {A₁ : Set l} {a₁ a₂ a₃ a₄ : A₁} (p : a₁ ≡ a₂) (q : a₃ ≡ a₄) → a₂ ≡ a₄ → p ≅ q
≡-≅-irrelevanceʳ refl refl refl = _≅_.refl

instance
  NumInt : Number ℤ
  NumInt .Number.Constraint _ = ⊤
  NumInt .Number.fromNat m = ℤ.pos m

instance
  NegNumInt : Negative ℤ
  NegNumInt .Negative.Constraint _ = ⊤
  NegNumInt .Negative.fromNeg zero    = ℤ.pos zero
  NegNumInt .Negative.fromNeg (suc m) = ℤ.negsuc m

instance
  ℤ-Dep+ : DependentMonoid+ ⊤ (\ _ -> ⊤) (\ _ _ -> ℤ)
  ℤ-Dep+ = record { _+_ = ℤ._+_; unit = \ _ -> ℤ.pos 0; identityˡ = ℤProp.+-identityˡ; identityʳ = ℤProp.+-identityʳ; assoc = ℤProp.+-assoc}


ℤmod-Rep : ℕ -> Set
ℤmod-Rep zero = ℤ
ℤmod-Rep (suc n) = ℕ

ℤmod-Cond : (n : ℕ) -> ℤmod-Rep n -> Set
ℤmod-Cond zero i = ⊤
ℤmod-Cond (suc n) i = i % suc n ≡ i

ℤmod : ℕ -> Set
ℤmod n = Σ[ i ∈ ℤmod-Rep n ] (ℤmod-Cond n i)

open import Relation.Nullary using (yes)

instance
  NumIntMod : ∀ {n} -> Number (ℤmod n)
  NumIntMod .Number.Constraint _ = ⊤
  NumIntMod {zero}  .Number.fromNat m = < ℤ.pos m , tt >
  NumIntMod {suc n} .Number.fromNat m = < m % suc n , DivMod.a%n%n≡a%n m n >

instance
  NegNumIntMod : ∀ {n} -> Negative (ℤmod n)
  NegNumIntMod .Negative.Constraint _ = ⊤
  NegNumIntMod {zero}  .Negative.fromNeg zero    = < ℤ.pos zero , tt >
  NegNumIntMod {zero}  .Negative.fromNeg (suc m) = < ℤ.negsuc m , tt >
  NegNumIntMod {suc n} .Negative.fromNeg m = < (suc n ℕ.∸ (m % suc n)) % suc n , DivMod.a%n%n≡a%n (suc n ℕ.∸ (m % suc n)) n >

addmod : ∀ {n} -> ℤmod n -> ℤmod n -> ℤmod n
addmod {zero}  < m₁ , _ > < m₂ , _ > = < m₁ + m₂ , tt >
addmod {suc n} < m₁ , _ > < m₂ , _ > = < m₁ + m₂ % suc n , DivMod.a%n%n≡a%n (m₁ + m₂) n >

addmod-assoc : ∀ {n} (i j k : ℤmod n) -> addmod (addmod i j) k ≡ addmod i (addmod j k)
addmod-assoc {zero} < i , tt > < j , tt > < k , tt > = cong (λ z → < z , tt >) (ℤProp.+-assoc i j k)
addmod-assoc {suc n} < i , eq₁ > < j , eq₂ > < k , eq₃ > = Pointwise-≡⇒≡ ( lem , ≡-≅-irrelevanceʳ _ _ lem )
  where lem : Σ.proj₁ (addmod (addmod < i , eq₁ > < j , eq₂ >) < k , eq₃ >)
              ≡ Σ.proj₁ (addmod < i , eq₁ > (addmod < j , eq₂ > < k , eq₃ >))
        lem = begin
          (i + j % m    ) + k       % m ≡⟨ DivMod.%-distribˡ-+ (_+_ i j % m) k n ⟩
          (i + j % m % m) + (k % m) % m ≡⟨ cong (λ z → _+_ z (k % m) % m) (a%n%n≡a%n (_+_ i j) n) ⟩
          (i + j % m    ) + (k % m) % m ≡⟨ sym (DivMod.%-distribˡ-+ (_+_ i j) k n) ⟩
          (i + j)     + k           % m ≡⟨ cong (_% m) (+-assoc i j k) ⟩
          i       + (j + k)         % m ≡⟨ DivMod.%-distribˡ-+ i (_+_ j k) n ⟩
          (i % m) + (j + k % m    ) % m ≡⟨ cong (λ z → _+_ (i % m) z % m) (sym (a%n%n≡a%n (_+_ j k) n)) ⟩
          (i % m) + (j + k % m % m) % m ≡⟨ sym (DivMod.%-distribˡ-+ i (j + k % m) n) ⟩
          i       + (j + k % m    ) % m ∎
          where m = suc n
instance
  ℤmod-Dep+ : ∀ {n} -> DependentMonoid+ ⊤ (\_ -> ⊤) (\ _ _ -> ℤmod n)
  ℤmod-Dep+ = record { _+_ = addmod; unit = \ _ -> 0; identityˡ = addmod-idˡ; identityʳ = addmod-idʳ; assoc = addmod-assoc }
    where addmod-idˡ : ∀ {n} (i : ℤmod n) -> addmod 0 i ≡ i
          addmod-idˡ {zero} < i , tt > = cong (λ z → < z , tt >) (ℤProp.+-identityˡ i)
          addmod-idˡ {suc n} < i , eq > = Pointwise-≡⇒≡ ( eq , ≡-≅-irrelevanceʳ _ _ eq )
          addmod-idʳ : ∀ {n} (i : ℤmod n) -> addmod i 0 ≡ i
          addmod-idʳ {zero} < i , tt > = cong (λ z → < z , tt >) (ℤProp.+-identityʳ i)
          addmod-idʳ {suc n} < i , eq > = Pointwise-≡⇒≡ ( eq' , ≡-≅-irrelevanceʳ _ _ eq' )
            where eq' : Σ.proj₁ (addmod < i , eq > 0) ≡ i
                  eq' rewrite +-comm i 0 = eq

raisem : ∀ {n} -> ℕ -> ℤmod n -> ℤmod n
raisem {zero} i < k , tt > = < ℤ.pos i ℤ.+ k , tt >
raisem {suc n} i < k , eq > = < (i ℕ.+ k) % suc n , DivMod.a%n%n≡a%n (i ℕ.+ k) n >

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

import Data.Nat.Properties as ℕProp 

[n+a]%n≢a : ∀ n a → (suc n + a) % suc n ≢ (suc n + a)
[n+a]%n≢a n a eq = ℕProp.<⇒≱ lem1 (subst (λ z → z ≥ suc n) (sym eq) lem2)
  where lem1 : (suc n + a) % suc n < suc n
        lem1 = DivMod.a%n<n (_+_ (suc n) a) n
        lem2 : suc n + a ≥ suc n
        lem2 = s≤s (ℕProp.≤-stepsʳ a ℕProp.≤-refl)


