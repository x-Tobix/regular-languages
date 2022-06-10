module Split where
open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)

data Split : Word {Alphabet} → Word {Alphabet} → Word {Alphabet} → Set where
  null  : (w : Word {Alphabet}) → Split w ε w
  cont : (l : Alphabet)(w : Word {Alphabet}){w1 w2 : Word {Alphabet}} → Split w w1 w2 → Split (l ∷ w) (l ∷ w1) w2