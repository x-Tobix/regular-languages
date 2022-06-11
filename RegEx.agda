module RegEx where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
open import Decidable using (Dec ; no ; yes)
open import List_lab using (List)
open import Conns using (⊥)
open import SplitDecidables using (decHasSplit; exists)
open import Split

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
  ∈⊕ : ∀ {w w₁ w₂ : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → Split.Split w w₁ w₂ → w₁ ∈ r₁ → w₂ ∈ r₂ → w ∈ (r₁ ⊕ r₂)
  ∈+ˡ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₁ → w ∈ (r₁ + r₂)
  ∈+ʳ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₂ → w ∈ (r₁ + r₂)
  ∈*₁ : ∀ {r : RegExp} → ε ∈ (r *)
  ∈*₂ : ∀ {a : Word {Alphabet}} → ∀ {r : RegExp} → a ∈ (r ⊕ (r *)) →  a ∈ (r *)

data ⨁Cont (r₁ r₂ : RegExp) (w₁ w₂ : Word {Alphabet}) : Set where
  get⨁Cont : w₁ ∈ r₁ → w₂ ∈ r₂ → ⨁Cont r₁ r₂ w₁ w₂

getεπ₁ : {r₁ r₂ : RegExp}{w₁ w₂ : Word {Alphabet}} → ⨁Cont r₁ r₂ w₁ w₂ → w₁ ∈ r₁
getεπ₁ (get⨁Cont ∈₁ _) = ∈₁

getεπ₂ : {r₁ r₂ : RegExp}{s₁ s₂ : Word{Alphabet}} → ⨁Cont r₁ r₂ s₁ s₂ → s₂ ∈ r₂
getεπ₂ (get⨁Cont _ ∈₂) = ∈₂

⊻ : {r r₂ : RegExp} → {w : Word {Alphabet}} → (w ∈ r → ⊥) → (w ∈ r₂ → ⊥) → w ∈ (r + r₂) → ⊥
⊻ l r₁ (∈+ˡ w) = l w
⊻ l r₁ (∈+ʳ w) = r₁ w

_∈?_ : (w : Word {Alphabet}) → (r : RegExp) → Dec (w ∈ r)

dec⊕ : (r₁ r₂ : RegExp)(s s₁ s₂ : Word {Alphabet})(sp : Split s s₁ s₂) → Dec (⨁Cont r₁ r₂ s₁ s₂)
        
dec⊕ r₁ r₂ s s₁ s₂ sp with s₁ ∈? r₁ | s₂ ∈? r₂
...| yes p | yes p₁ = yes (get⨁Cont p p₁)
...| yes p | no ¬p = no (λ p → ¬p (getεπ₂ p))
...| no ¬p | yes p = no (λ p → ¬p (getεπ₁ p))
...| no ¬p | no ¬p₁ = no (λ p → ¬p (getεπ₁ p))

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

w ∈? (r₁ + r₂) with w ∈? r₁ | w ∈? r₂
...| yes t₁ | yes  t₂ = yes (∈+ˡ t₁)
...| yes t₁ | no t₂ = yes (∈+ˡ t₁)
...| no t₁ | yes t₂ = yes (∈+ʳ t₂)
...| no t₁ | no t₂ = no (λ x → ⊻ t₁ t₂ x)

w ∈? (r₁ ⊕ r₂) with decHasSplit w (dec⊕ r₁ r₂ w)
...| yes (exists s₁ s₂ sp (get⨁Cont x x₁)) = yes (∈⊕ {w} {s₁} {s₂} {r₁} {r₂} sp x x₁)
w ∈? (r₁ ⊕ r₂) | no ¬p = no contra
  where contra : w ∈ (r₁ ⊕ r₂) → ⊥
        contra (∈⊕ {w} {s₁} {s₂} {r₁} {r₂} x p p₁) = ¬p (exists s₁ s₂ x (get⨁Cont p p₁))
  