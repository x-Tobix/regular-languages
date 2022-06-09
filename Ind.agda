module Ind where

import Equality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Naturals using (ℕ; zero; suc; _+_; _∙_; _∸_; Bin; from; inc; ⟨⟩; _O; _I)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
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

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

∙-distrib-+ : ∀ (m n p : ℕ) → (m + n) ∙ p ≡ m ∙ p + n ∙ p
∙-distrib-+ zero n p = refl
∙-distrib-+ (suc m) n p rewrite ∙-distrib-+ m n p | +-assoc p (m ∙ p) (n ∙ p) = refl

∙-assoc :  ∀ (m n p : ℕ) → (m ∙ n) ∙ p ≡ m ∙ (n ∙ p)
∙-assoc zero n p = refl
∙-assoc (suc m) n p rewrite ∙-distrib-+ n (m ∙ n) p | ∙-assoc m n p = refl

∙-zeroʳ :  ∀ (n : ℕ) → n ∙ zero ≡ zero
∙-zeroʳ zero = refl
∙-zeroʳ (suc n) rewrite ∙-zeroʳ n = refl

∙-suc :  ∀ (m n : ℕ) → m ∙ suc n ≡ m + (m ∙ n)
∙-suc zero n = refl
∙-suc (suc m) n rewrite ∙-suc m n | sym(+-assoc n m (m ∙ n)) | +-comm n m  | +-assoc m n (m ∙ n)  = refl

∙-comm : ∀ (m n : ℕ) → m ∙ n ≡ n ∙ m
∙-comm m zero rewrite ∙-zeroʳ m = refl
∙-comm m (suc n) rewrite ∙-suc m n | ∙-comm m n = refl


from-hom : ∀ {b : Bin} → from (inc b) ≡ suc (from b)
from-hom {⟨⟩} = refl
from-hom {b O} rewrite +-identityʳ (from b) | +-comm (from b + from b) 1 = refl
from-hom {b I} rewrite +-identityʳ (from b) | +-identityʳ (from (inc b)) | from-hom {b} | +-comm (from b + from b) 1 | +-suc (from b) (from b) = refl
