module Rels where

import Equality as Eq
open Eq using (_≡_; refl; cong)

open import Naturals using (ℕ; zero; suc; _+_; _∙_)
open import Ind using (+-comm; +-identityʳ; ∙-distrib-+; ∙-comm )

data _≤_ : ℕ → ℕ → Set where
 z≤n : ∀ {n : ℕ} → zero ≤ n
 s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

infix 4 _≤_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
 → m ≤ n
 → n ≤ p
 → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

≤-antisym : ∀ {m n : ℕ}
 → m ≤ n
 → n ≤ m
 → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x) (s≤s y) = cong suc (≤-antisym x y)


data Total (m n : ℕ) : Set where
  forward :
    m ≤ n
    → Total m n

  backward :
    n ≤ m
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = backward z≤n 
≤-total (suc m) (suc n) with ≤-total m n
...| forward x = forward (s≤s x)
...| backward y = backward (s≤s y)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  backward z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n)  =  forward (s≤s m≤n)
    helper (backward n≤m)  =  backward (s≤s n≤m)

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ}
        → odd n
        → even(suc n)

data odd where
  suc : ∀ {n : ℕ}
       → even n
       → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
  → even (m + n)

e+e≡e zero zero = zero
e+e≡e zero (suc x) = suc x
e+e≡e (suc (suc x)) y = suc (suc (e+e≡e x y))

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
  → odd (m + n)

o+e≡o (suc x) en = suc (e+e≡e x en)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q

+-mono-≤ {m} {n} {p} {q} m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)  


∙-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n ∙ p ≤ n ∙ q
∙-monoʳ-≤ zero    p q p≤q  =  z≤n
∙-monoʳ-≤ (suc n) p q p≤q  = +-mono-≤ p≤q (∙-monoʳ-≤ n p q p≤q)

∙-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m ∙ p ≤ n ∙ p
∙-monoˡ-≤ m n p m≤n  rewrite ∙-comm m p | ∙-comm n p  = ∙-monoʳ-≤ p m n m≤n 

∙-mono-≤ :  ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
    -------------
  → m ∙ p ≤ n ∙ q

∙-mono-≤ {m} {n} {p} {q} m≤n p≤q =  ≤-trans (∙-monoˡ-≤ m n p m≤n) (∙-monoʳ-≤ n p q p≤q)

≤-suc : ∀ { n m : ℕ}
  → suc n ≤ m
  → n ≤ m
≤-suc {zero} {.(suc _)} (s≤s sn≤m) = z≤n
≤-suc {suc n} {.(suc _)} (s≤s {suc n} {n₁} sn≤m) = s≤s (≤-suc sn≤m)

data _<_ : ℕ → ℕ → Set where
 z<s : ∀ {n : ℕ} → zero < suc n
 s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ}
 → m < n
 → n < p
 → m < p

<-trans z<s (s<s _) = z<s
<-trans (s<s x) (s<s y) = s<s (<-trans x y)

data Trichotomy (m n : ℕ) : Set where
  forward :
    m < n
    → Trichotomy m n

  backward :
    n < m
    → Trichotomy m n

  equal :
    n ≡ m
    → Trichotomy m n


<-tri : ∀ (m n : ℕ) → Trichotomy m n
<-tri zero zero = equal refl
<-tri zero (suc n) = forward z<s
<-tri (suc m) zero = backward z<s
<-tri (suc m) (suc n) with <-tri m n
...| forward x = forward (s<s x)
...| backward y = backward (s<s y)
...| equal z = equal (cong suc z)
