module RegEx where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_; _^_)
open import Naturals using (ℕ)
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


example1 : (a ∷ (b ∷ ε)) ∈ ((literal a) ⊕ (literal b))
example1 = ∈⊕ {(a ∷ (b ∷ ε))} {a ∷ ε} {b ∷ ε} (cont a (b ∷ ε) (null (b ∷ ε))) (∈literal {a}) (∈literal {b})

example2 : ((a ∷ ε) ^ 2) ∈ ((literal a) *)
example2 = ∈*₂ (∈⊕ {a ∷ (a ∷ ε)} {a ∷ ε} {a ∷ ε} (cont a (a ∷ ε) (null (a ∷ ε))) ∈literal (∈*₂ (∈⊕ {a ∷ ε} {a ∷ ε} {ε} (cont a ε (null ε)) ∈literal ∈*₁)))


data ⨁Cont (r₁ r₂ : RegExp) (w₁ w₂ : Word {Alphabet}) : Set where
  get⨁Cont : w₁ ∈ r₁ → w₂ ∈ r₂ → ⨁Cont r₁ r₂ w₁ w₂

data *Cont (r : RegExp) :  Word {Alphabet} →  Word {Alphabet} → Set where
  get*Cont : (c : Alphabet)(w₁ w₂ : Word {Alphabet}) → (c ∷ w₁) ∈ r → w₂ ∈ (r *)→ *Cont r (c ∷ w₁) w₂

get⊕r₁ : {r₁ r₂ : RegExp}{w₁ w₂ : Word {Alphabet}} → ⨁Cont r₁ r₂ w₁ w₂ → w₁ ∈ r₁
get⊕r₁ (get⨁Cont ∈₁ _) = ∈₁

get⊕r₂ : {r₁ r₂ : RegExp}{s₁ s₂ : Word{Alphabet}} → ⨁Cont r₁ r₂ s₁ s₂ → s₂ ∈ r₂
get⊕r₂ (get⨁Cont _ ∈₂) = ∈₂

get*r₁ : {r : RegExp}{s₁ s₂ :  Word{Alphabet}} → *Cont r s₁ s₂ → s₁ ∈ r
get*r₁ (get*Cont _ _ _ ∈₁ ∈₂) = ∈₁

get*r₂ : {r : RegExp}{s₁ s₂ :  Word{Alphabet}} → *Cont r s₁ s₂ → s₂ ∈ (r *)
get*r₂ (get*Cont _ _ _ ∈₁ ∈₂) = ∈₂

⊻ : {r r₂ : RegExp} → {w : Word {Alphabet}} → (w ∈ r → ⊥) → (w ∈ r₂ → ⊥) → w ∈ (r + r₂) → ⊥
⊻ l r₁ (∈+ˡ w) = l w
⊻ l r₁ (∈+ʳ w) = r₁ w

_∈?_ : (w : Word {Alphabet}) → (r : RegExp) → Dec (w ∈ r)

dec⊕ : (r₁ r₂ : RegExp)(s s₁ s₂ : Word {Alphabet})(sp : Split s s₁ s₂) → Dec (⨁Cont r₁ r₂ s₁ s₂)    
dec⊕ r₁ r₂ s s₁ s₂ sp with s₁ ∈? r₁ | s₂ ∈? r₂
...| yes p | yes p₁ = yes (get⨁Cont p p₁)
...| yes p | no ¬p = no (λ p → ¬p (get⊕r₂ p))
...| no ¬p | yes p = no (λ p → ¬p (get⊕r₁ p))
...| no ¬p | no ¬p₁ = no (λ p → ¬p (get⊕r₁ p))

{-# NON_TERMINATING #-}
dec* : (r : RegExp)(s s₁ s₂ :  Word {Alphabet})(sp : Split s s₁ s₂) → Dec (*Cont r s₁ s₂)
dec* r s .ε .s (null .s) = no (λ ())
dec* r ._ (l ∷ s₁) s₂ (cont l s sp) with (l ∷ s₁) ∈? r | s₂ ∈? (r *)
...| yes p₁ | yes p₂ = yes (get*Cont l s₁ s₂ p₁ p₂)
...| yes p  | no ¬p  = no (λ p → ¬p (get*r₂ p))
...| no ¬p  | _      = no (λ p → ¬p( get*r₁ p))

-- Zaczynamy definiowac _∈?_
w ∈? ∅ = no (λ ())

ε ∈? Ε = yes ∈Ε
(x ∷ w) ∈? Ε = no (λ ())

ε ∈? (literal x) = no (λ ())
(a ∷ ε) ∈? (literal a) = yes ∈literal
(a ∷ ε) ∈? (literal b) = no (λ ())
(b ∷ ε) ∈? (literal a) = no (λ ())
(b ∷ ε) ∈? (literal b) = yes ∈literal
(w₁ ∷ (w₂ ∷ ws)) ∈? (literal x) = no (λ ())

w ∈? (r₁ + r₂) with w ∈? r₁ | w ∈? r₂
...| yes t₁ | yes  t₂ = yes (∈+ˡ t₁)
...| yes t₁ | no t₂ = yes (∈+ˡ t₁)
...| no t₁ | yes t₂ = yes (∈+ʳ t₂)
...| no t₁ | no t₂ = no (λ x → ⊻ t₁ t₂ x)

w ∈? (r₁ ⊕ r₂) with decHasSplit w (dec⊕ r₁ r₂ w)
...| yes (exists s₁ s₂ sp (get⨁Cont x x₁)) = yes (∈⊕ {w} {s₁} {s₂} {r₁} {r₂} sp x x₁)
...| no ¬p = no contra
  where contra : w ∈ (r₁ ⊕ r₂) → ⊥
        contra (∈⊕ {w} {s₁} {s₂} {r₁} {r₂} x p p₁) = ¬p (exists s₁ s₂ x (get⨁Cont p p₁))
  
ε ∈? (r *) = yes ∈*₁
(x ∷ w) ∈? (r *) with decHasSplit (x ∷ w) (dec* r (x ∷ w))
...| yes (exists .(l ∷ w₁) s₂ sp (get*Cont l w₁ .s₂ x₁ x₂)) = yes (∈*₂ (∈⊕ sp x₁ x₂))
...| no ¬p = no contra
  where contra : (x ∷ w) ∈ (r *) → ⊥
        contra (∈*₂ (∈⊕ (null .(x ∷ w)) ε∈r xw∈r*)) = contra xw∈r*
        contra (∈*₂ {x ∷ w} {r} (∈⊕ (cont .x .w sp) xw∈r w2∈r*)) = ¬p (exists (x ∷ _) _ (cont x w sp) (get*Cont x _ _ xw∈r w2∈r*))
