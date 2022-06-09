module RegEx where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
open import Decidable using (Dec ; no ; yes)
open import List_lab using (List)

data RegExp : Set where
    ∅ : RegExp                       -- Empty set
    Ε : RegExp                        -- Empty word
    literal : Alphabet → RegExp      -- literal
    _* : RegExp → RegExp             -- Kleene star
    _⊕_ : RegExp → RegExp → RegExp  -- Concatenation
    _+_ : RegExp → RegExp → RegExp   -- Sum

data _∈_ :  Word {Alphabet} → RegExp → Set where
  ∈Ε : ε ∈ Ε
  ∈literal : ∀ {a} → (a ∷ ε) ∈ (literal a)
  ∈⊕ : ∀ {a b : Word {Alphabet}} → ∀ {r1 r2 : RegExp} → a ∈ r1 → b ∈ r2 → (a ++ b) ∈ (r1 ⊕ r2)
  ∈+ˡ : ∀ {w : Word {Alphabet}} → ∀ {r1 r2 : RegExp} → w ∈ r1 → w ∈ (r1 + r2)
  ∈+ʳ : ∀ {w : Word {Alphabet}} → ∀ {r1 r2 : RegExp} → w ∈ r2 → w ∈ (r1 + r2)
  ∈*₁ : ∀ {r : RegExp} → ε ∈ (r *)
  ∈*₂ : ∀ {a : Word {Alphabet}} → ∀ {r : RegExp} → a ∈ (r ⊕ (r *)) →  a ∈ (r *)

_∈?_ : (w : Word {Alphabet}) → (r : RegExp) → Dec (w ∈ r)
w ∈? ∅ = no (λ ())

ε ∈? Ε = yes ∈Ε
(x ∷ w) ∈? Ε = no (λ ())

ε ∈? (literal x) = no (λ ())
(a ∷ ε) ∈? (literal a) = yes ∈literal
(a ∷ ε) ∈? (literal b) = no (λ ())
(b ∷ ε) ∈? (literal a) = no (λ ())
(b ∷ ε) ∈? (literal b) = yes ∈literal
(w1 ∷ (w2 ∷ ws)) ∈? (literal x) = no (λ ())

ε ∈? (r *) = yes ∈*₁
(x ∷ w) ∈? (r *) = {!!}

ε ∈? (r1 ⊕ r2) with ε ∈? r1 | ε ∈? r2
...| yes t1 | yes t2 = yes (∈⊕ t1 t2)
...| yes t1 | no t2 = no {!!}
...| no t1 | yes t2 = no {!!}
...| no t1 | no t2 = no {!!}

(x ∷ w) ∈? (r1 ⊕ r2) with (x ∷ ε) ∈? r1 | w ∈? r2
...| yes t1 | yes t2 = yes (∈⊕ t1 t2)
...| yes t1 | no t2 = no {!!}
...| no t1 | yes t2 = no {!!}
...| no t1 | no t2 = no {!!}

w ∈? (r1 + r2) with w ∈? r1 | w ∈? r2
...| yes t1 | yes  t2 = yes (∈+ˡ t1)
...| yes t1 | no t2 = yes (∈+ˡ t1)
...| no t1 | yes t2 = yes (∈+ʳ t2)
...| no t1 | no t2 = no {!!}
