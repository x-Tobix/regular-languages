module Naturals where

import Equality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc z + y = suc ( z + y )

_∙_ : ℕ → ℕ → ℕ 
zero ∙ y = zero
suc x ∙ y = y + ( x ∙ y )

infixl 6 _+_ _∸_
infixl 7 _∙_

theorem : 1 + 1 ≡ 2
theorem =
 begin
  1 + 1
 ≡⟨⟩
  ( suc zero ) + 1
 ≡⟨⟩
  suc ( zero + 1 )
 ≡⟨⟩
  suc 1
 ≡⟨⟩
  2
 ∎

_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
x ^ suc y = x ∙ (x ^ y)

infixr 8 _^_

_ : 2 ^ 3 ≡ 8
_ = refl

_∸_ : ℕ → ℕ → ℕ
zero ∸ y = zero
suc x ∸ zero = suc x
suc x ∸ suc y = x ∸ y

_ : 2 ∸ 3 ≡ 0
_ = refl

_ : 2 ∸ 2 ≡ 0
_ = refl

_ : 2 ∸ 1 ≡ 1
_ = refl


data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O 

_ : inc(⟨⟩ I I ) ≡ ⟨⟩ I O O
_ = refl 

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 2 ≡ ⟨⟩ I O
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (a O) = 2 ∙ (from a)
from (a I) =  2 ∙ from a + 1

_ : from (⟨⟩ I I )  ≡ 3
_ = refl
