module Split where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
import Equality as Eq
open Eq using (_≡_; refl)

data Split : Word {Alphabet} → Word {Alphabet} → Word {Alphabet} → Set where
  null  : (w : Word {Alphabet}) → Split w ε w
  cont : (l : Alphabet)(w : Word {Alphabet}){w1 w2 : Word {Alphabet}} → Split w w1 w2 → Split (l ∷ w) (l ∷ w1) w2

-- Poprawnosc definicji
-- Chcemy Split w w1 w1 <=> l = w1++w2
⇒ : (w w1 w2 : Word {Alphabet}) → Split w w1 w2 → w ≡ (w1 ++ w2)
⇒ w ε .w (null .w) = refl
⇒ (x ∷ w) (x ∷ w1) w2 (cont x w sp) rewrite ⇒ _ w1 w2 sp = refl

⇐ : (w w1 w2 : Word {Alphabet}) → w ≡ (w1 ++ w2) → Split w w1 w2
⇐ w ε .w refl = null w
⇐ .(x ∷ (w1 ++ w2)) (x ∷ w1) w2 refl = cont x (w1 ++ w2) (⇐ _ w1 w2 refl)
