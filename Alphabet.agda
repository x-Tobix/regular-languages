module Alphabet where

open import Naturals using (ℕ; zero; suc; _+_)

data Alphabet : Set where
    a : Alphabet
    b : Alphabet

data Word {A : Set} : Set where
  ε : Word
  _∷_ : A → Word {A} → Word {A}

-- konkatenacja slow
_++_ : ∀ {A : Set} → Word {A} → Word {A} → Word {A}
ε ++ w = w
(s ∷ w₁) ++ w₂  =  s ∷ (w₁ ++ w₂)

-- potega
_^_ : ∀ {A : Set} → Word {A} → ℕ → Word {A}
w ^ zero = ε
w ^ suc zero = w
w ^ suc (suc k) = w ++ (w ^ (suc k))

-- Word length
length : (w : Word {Alphabet}) → ℕ
length ε = zero
length (x ∷ w) = 1 + (length w)
