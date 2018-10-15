
module Data.IntMod where

open import Data.Unit
open import Data.Product as Σ

open import Data.Nat as ℕ using (ℕ; zero; suc; _<_; _>_; _≤_; _≥_)
open import Data.Nat.Properties

open import Data.Integer as ℤ using (ℤ)
open import Data.Integer.Properties as ℤProp using ()

open import Data.Nat.DivMod public

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- An integer mod n is a natural number k such that k % n ≡ k (or if n = 0, an integer k)
-- We don't just define ℤmod 0 ≡ ℤ to avoid overlapping instances of _+_

ℤmod-Rep : ℕ -> Set
ℤmod-Rep zero = ℤ
ℤmod-Rep (suc n) = ℕ

ℤmod-Cond : (n : ℕ) -> ℤmod-Rep n -> Set
ℤmod-Cond zero i = ⊤
ℤmod-Cond (suc n) i = i % suc n ≡ i

ℤmod : ℕ -> Set
ℤmod n = Σ[ i ∈ ℤmod-Rep n ] (ℤmod-Cond n i)

-- Equality on ℤmod n can be reduced to equality on ℤmod-Rep

open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Data.Product.Relation.Pointwise.Dependent as Dep using (Pointwise-≡⇒≡)

≡-≅-irrelevanceʳ : ∀ {l} {A₁ : Set l} {a₁ a₂ a₃ a₄ : A₁} (p : a₁ ≡ a₂) (q : a₃ ≡ a₄) → a₂ ≡ a₄ → p ≅ q
≡-≅-irrelevanceʳ refl refl refl = _≅_.refl

≡-on-rep : ∀ {n} {i j : ℤmod n} -> proj₁ i ≡ proj₁ j -> i ≡ j
≡-on-rep {zero} {i , tt} {j , tt} eq = cong (λ z → z , tt) eq
≡-on-rep {suc n} {i , eq₁} {j , eq₂} eq = Pointwise-≡⇒≡ ( eq Dep., ≡-≅-irrelevanceʳ _ _ eq )


-- Basic operations on ℤmod n

-- addition mod n
_+_ : ∀ {n} -> ℤmod n -> ℤmod n -> ℤmod n
_+_ {zero}  (m₁ , _) (m₂ , _) = (m₁ ℤ.+ m₂ , tt)
_+_ {suc n} (m₁ , _) (m₂ , _) = ((m₁ ℕ.+ m₂) % suc n , a%n%n≡a%n (m₁ ℕ.+ m₂) n)

zero-modn : ∀ {n} -> ℤmod n
zero-modn {zero} = (ℤ.pos 0 , tt)
zero-modn {suc _} = (0 , refl)

-- the action of ℕ on ℤmod n
raisem : ∀ {n} -> ℕ -> ℤmod n -> ℤmod n
raisem {zero} i (k , tt) = (ℤ.+ i ℤ.+ k , tt)
raisem {suc n} i (k , eq) = ((i ℕ.+ k) % suc n , a%n%n≡a%n (i ℕ.+ k) n)

inc : ∀ {n} -> ℤmod n -> ℤmod n
inc {zero} = map₁ ℤ.suc
inc {suc n} = raisem 1

dec : ∀ {n} -> ℤmod n -> ℤmod n
dec {zero} = map₁ ℤ.pred
dec {suc n} = raisem n

-- inc and dec are indeed inverses (this is another way to define ℤmod n if we had HITs)

raisem-actson : ∀ {n} i j (k : ℤmod n) -> raisem i (raisem j k) ≡ raisem (i ℕ.+ j) k
raisem-actson {zero} i j (k , tt) = ≡-on-rep (sym (ℤProp.+-assoc (ℤ.pos i) (ℤ.pos j) k))
raisem-actson {suc n} i j (k , eq) = ≡-on-rep lem
  where lem : Σ.proj₁ (raisem i (raisem j (k , eq))) ≡ Σ.proj₁ (raisem (i ℕ.+ j) (k , eq))
        lem = begin
          ( i      ℕ.+  ((j ℕ.+ k) % m)     ) % m ≡⟨ %-distribˡ-+ i ((j ℕ.+ k) % m) n ⟩
          ((i % m) ℕ.+ (((j ℕ.+ k) % m) % m)) % m ≡⟨ cong (λ z → ((i % m) ℕ.+ z) % m) (a%n%n≡a%n (j ℕ.+ k) n) ⟩
          ((i % m) ℕ.+  ((j ℕ.+ k) % m)     ) % m ≡⟨ sym (%-distribˡ-+ i (j ℕ.+ k) n) ⟩
          ( i      ℕ.+   (j ℕ.+ k)          ) % m ≡⟨ cong (_% m) (sym (+-assoc i j k)) ⟩
          ((i      ℕ.+   j) ℕ.+ k           ) % m ∎
          where m = suc n

inv-inc-dec : ∀ {n} (i : ℤmod n) -> inc (dec i) ≡ i
inv-inc-dec {zero} (ℤ.pos zero , tt) = refl
inv-inc-dec {zero} (ℤ.pos (suc _) , tt) = refl
inv-inc-dec {zero} (ℤ.negsuc _ , tt) = refl
inv-inc-dec {suc n} (i , eq) = ≡-on-rep lem
  where lem : Σ.proj₁ (inc (dec (i , eq))) ≡ i
        lem = begin
          Σ.proj₁ (raisem 1 (raisem n (i , eq))) ≡⟨ cong Σ.proj₁ (raisem-actson 1 n (i , eq)) ⟩
          Σ.proj₁ (raisem (1 ℕ.+ n) (i , eq))    ≡⟨ refl ⟩
          ((suc n) ℕ.+ i) % suc n                ≡⟨ cong (_% suc n) (Data.Nat.Properties.+-comm (suc n) i) ⟩
          (i ℕ.+ (suc n)) % suc n                ≡⟨ [a+n]%n≡a%n i n ⟩
          i % suc n                              ≡⟨ eq ⟩
          i                                      ∎

inv-dec-inc : ∀ {n} (i : ℤmod n) -> dec (inc i) ≡ i
inv-dec-inc {zero} (ℤ.pos _ , tt) = refl
inv-dec-inc {zero} (ℤ.negsuc zero , tt) = refl
inv-dec-inc {zero} (ℤ.negsuc (suc _) , tt) = refl
inv-dec-inc {suc n} (i , eq) = ≡-on-rep lem
  where lem : Σ.proj₁ (dec (inc  (i , eq))) ≡ i
        lem = begin
          Σ.proj₁ (raisem n (raisem 1 (i , eq))) ≡⟨ cong Σ.proj₁ (raisem-actson n 1 (i , eq)) ⟩
          Σ.proj₁ (raisem (n ℕ.+ 1) (i , eq))      ≡⟨ cong (\ z -> Σ.proj₁ (raisem z (i , eq))) (+-comm n 1) ⟩
          Σ.proj₁ (raisem (1 ℕ.+ n) (i , eq))      ≡⟨ refl ⟩
          ((suc n) ℕ.+ i) % suc n                  ≡⟨ cong (_% suc n) (Data.Nat.Properties.+-comm (suc n) i) ⟩
          (i ℕ.+ (suc n)) % suc n                  ≡⟨ [a+n]%n≡a%n i n ⟩
          i % suc n                                ≡⟨ eq ⟩
          i                                        ∎

