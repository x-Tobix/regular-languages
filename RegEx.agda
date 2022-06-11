module RegEx where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
open import Decidable using (Dec ; no ; yes)
open import List_lab using (List)
open import Conns using (⊥)

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
  ∈⊕ : ∀ {a b : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → a ∈ r₁ → b ∈ r₂ → (a ++ b) ∈ (r₁ ⊕ r₂)
  ∈+ˡ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₁ → w ∈ (r₁ + r₂)
  ∈+ʳ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₂ → w ∈ (r₁ + r₂)
  ∈*₁ : ∀ {r : RegExp} → ε ∈ (r *)
  ∈*₂ : ∀ {a : Word {Alphabet}} → ∀ {r : RegExp} → a ∈ (r ⊕ (r *)) →  a ∈ (r *)

⊻ : {r r₂ : RegExp} → {w : Word {Alphabet}} → (w ∈ r → ⊥) → (w ∈ r₂ → ⊥) → w ∈ (r + r₂) → ⊥
⊻ l r₁ (∈+ˡ w) = l w
⊻ l r₁ (∈+ʳ w) = r₁ w

_∈?_ : (w : Word {Alphabet}) → (r : RegExp) → Dec (w ∈ r)
w ∈? ∅ = no (λ ())

ε ∈? Ε = yes ∈Ε
(x ∷ w) ∈? Ε = no (λ ())

ε ∈? (literal x) = no (λ ())
(a ∷ ε) ∈? (literal a) = yes ∈literal
(a ∷ ε) ∈? (literal b) = no (λ ())
(b ∷ ε) ∈? (literal a) = no (λ ())
(b ∷ ε) ∈? (literal b) = yes ∈literal
(w₁ ∷ (w₂ ∷ ws)) ∈? (literal x) = no (λ ())

ε ∈? (r *) = yes ∈*₁
(x ∷ w) ∈? (r *) = {!!}

ε ∈? (r₁ ⊕ r₂) with ε ∈? r₁ | ε ∈? r₂
...| yes t₁ | yes t₂ = yes (∈⊕ t₁ t₂)
...| yes t₁ | no t₂ = no {!!}
...| no t₁ | yes t₂ = no {!!}
...| no t₁ | no t₂ = no {!!}

(x ∷ w) ∈? (r₁ ⊕ r₂) with (x ∷ ε) ∈? r₁ | w ∈? r₂
...| yes t₁ | yes t₂ = yes (∈⊕ t₁ t₂)
...| yes t₁ | no t₂ = no {!!}
...| no t₁ | yes t₂ = no {!!}
...| no t₁ | no t₂ = no {!!}

w ∈? (r₁ + r₂) with w ∈? r₁ | w ∈? r₂
...| yes t₁ | yes  t₂ = yes (∈+ˡ t₁)
...| yes t₁ | no t₂ = yes (∈+ˡ t₁)
...| no t₁ | yes t₂ = yes (∈+ʳ t₂)
...| no t₁ | no t₂ = no (λ x → ⊻ t₁ t₂ x)
  