module Equals where

data _≡_ : ∀ {A : Set} → A → A → Set where
  refl : ∀ { A : Set } → ∀ { x : A } → x ≡ x
 
infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  → y ≡ x
  
sym refl = refl


trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
  
trans refl refl = refl


cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y

cong f refl = refl


cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y

cong₂ f refl refl = refl


cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
  → ∀ (x : A) → f x ≡ g x

cong-app refl g = refl

cong-app' : ∀ {A B : Set} {f g : A → B} {x y : A}
  → f ≡ g
  → x ≡ y
  → f x ≡ g y

cong-app' refl refl = refl

cong₂' : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y

cong₂' f u≡x v≡y = cong-app' (cong f u≡x) v≡y 


subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  → P x → P y

subst P refl Px = Px


module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ { x y : A}
    → x ≡ y
    → x ≡ y

  begin r = r

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    → x ≡ y

  x ≡⟨⟩ r = r

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z

  x ≡⟨ r1 ⟩ r2 = trans r1 r2


  _∎ : ∀ (x : A)
    → x ≡ x

  x ∎ = refl

  
open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc z + y = suc ( z + y )

infixl 6 _+_

postulate
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-identity : ∀ (n : ℕ) → n + zero ≡ n

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = 
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
infix 4 _≤_
  
module ≤-Reasoning where
  
  postulate
    ≤-trans : ∀ {m n p : ℕ}
      → m ≤ n
      → n ≤ p
      → m ≤ p
    ≤-refl : ∀ {n : ℕ} → n ≤ n

  infix 1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _≤-∎

  ≤-begin_ : ∀ { x y : ℕ}
    → x ≤ y
    → x ≤ y

  ≤-begin r = r

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
    → x ≤ y

  x ≤⟨⟩ r = r

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
    → x ≤ z

  x ≤⟨ r1 ⟩ r2 = ≤-trans r1 r2


  _≤-∎ : ∀ (x : ℕ)
    → x ≤ x

  x ≤-∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q = 
  ≤-begin
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ≤-∎
+-monoʳ-≤ (suc n) p q p≤q = 
  ≤-begin
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤-∎

≡-≤ : ∀ {m n : ℕ}
  → m ≡ n
  → m ≤ n

≡-≤ {m} {n} m≡n = {!!}

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n =
  ≤-begin
    m + p
  ≤⟨ ≡-≤ (+-comm m p) ⟩
    p + m
  ≤⟨  +-monoʳ-≤ p m n m≤n  ⟩
    p + n
  ≤⟨ ≡-≤ (+-comm p n) ⟩
    n + p
  ≤-∎
