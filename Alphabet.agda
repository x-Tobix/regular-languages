module Alphabet where

data Alphabet : Set where
    a : Alphabet
    b : Alphabet

data Word {A : Set} : Set where
  ε : Word
  _∷_ : A → Word {A} → Word {A}

-- sklejenie slow
_++_ : ∀ {A : Set} → Word {A} → Word {A} → Word {A}
ε       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
