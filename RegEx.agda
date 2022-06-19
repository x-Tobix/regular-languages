module RegEx where

open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_; _^_)
open import Naturals using (ℕ)
open import Decidable using (Dec ; no ; yes)
open import List_lab using (List)
open import Conns using (⊥)
open import SplitDecidables using (∈?Split; ∃)
open import Split

-- Typ danych reprezentujacy wyrazenia regularne
data RegExp : Set where
    ∅ : RegExp                       -- Empty set
    Ε : RegExp                        -- Empty word
    literal : Alphabet → RegExp      -- literal
    _* : RegExp → RegExp             -- Kleene star
    _⊕_ : RegExp → RegExp → RegExp  -- Concatenation
    _+_ : RegExp → RegExp → RegExp   -- Sum

-- Typ danych mowiacy o przynaleznosci danego slowa do jezyka generowanego przez dane wyrazenie regularne
data _∈_ :  Word {Alphabet} → RegExp → Set where
  ∈Ε : ε ∈ Ε
  ∈literal : ∀ {a} → (a ∷ ε) ∈ (literal a)
  ∈⊕ : ∀ {w w₁ w₂ : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → Split.Split w w₁ w₂ → w₁ ∈ r₁ → w₂ ∈ r₂ → w ∈ (r₁ ⊕ r₂)
  ∈+ˡ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₁ → w ∈ (r₁ + r₂)
  ∈+ʳ : ∀ {w : Word {Alphabet}} → ∀ {r₁ r₂ : RegExp} → w ∈ r₂ → w ∈ (r₁ + r₂)
  ∈*₁ : ∀ {r : RegExp} → ε ∈ (r *)
  ∈*₂ : ∀ {a : Word {Alphabet}} → ∀ {r : RegExp} → a ∈ (r ⊕ (r *)) →  a ∈ (r *)

-- Łączność sumy wyrażeń regularnych
+conn : {w : Word {Alphabet}} → {r₁ r₂ r₃ : RegExp} → w ∈ (r₁ + (r₂ + r₃)) → w ∈ ((r₁ + r₂) + r₃)
+conn (∈+ˡ w) = ∈+ˡ (∈+ˡ w)
+conn (∈+ʳ (∈+ˡ w)) = ∈+ˡ (∈+ʳ w)
+conn (∈+ʳ (∈+ʳ w)) = ∈+ʳ w

-- Przemienność sumy wyrażeń regularnych
+alt : {w : Word {Alphabet}} → {r₁ r₂ : RegExp} → w ∈ (r₁ + r₂) → w ∈ (r₂ + r₁)
+alt (∈+ˡ w) = ∈+ʳ w
+alt (∈+ʳ w) = ∈+ˡ w

-- Przyklady wykorzystania
example1 : (a ∷ (b ∷ ε)) ∈ ((literal a) ⊕ (literal b))
example1 = ∈⊕ {(a ∷ (b ∷ ε))} {a ∷ ε} {b ∷ ε} (cont a (b ∷ ε) (null (b ∷ ε))) (∈literal {a}) (∈literal {b})

example2 : ((a ∷ ε) ^ 2) ∈ ((literal a) *)
example2 = ∈*₂ (∈⊕ {a ∷ (a ∷ ε)} {a ∷ ε} {a ∷ ε} (cont a (a ∷ ε) (null (a ∷ ε))) ∈literal (∈*₂ (∈⊕ {a ∷ ε} {a ∷ ε} {ε} (cont a ε (null ε)) ∈literal ∈*₁)))

example3 : (a ∷ ε) ∈ ((literal a) + (literal b))
example3 = ∈+ˡ ∈literal

example4 : (b ∷ ε) ∈ ((literal a) + (literal b))
example4 = ∈+ʳ ∈literal

-- Funkcje pomocnicze
-- Typ reprezentujacy wyrazenia regularne generujace poczatek i koniec slowa w przypadku konkatenacji oraz te slowa
data ⨁Cont (r₁ r₂ : RegExp) (w₁ w₂ : Word {Alphabet}) : Set where
  get⨁Cont : w₁ ∈ r₁ → w₂ ∈ r₂ → ⨁Cont r₁ r₂ w₁ w₂

-- Typ reprezentujacy wyrazenie regularne oraz poczatek i koniec slowa w przypadku, gdy ich konkatenacja nalezy do gwiazki Kleenego tego wyrazenia
data *Cont (r : RegExp) :  Word {Alphabet} →  Word {Alphabet} → Set where
  get*Cont : (c : Alphabet)(w₁ w₂ : Word {Alphabet}) → (c ∷ w₁) ∈ r → w₂ ∈ (r *)→ *Cont r (c ∷ w₁) w₂

-- Funkcja zwracajaca dowod, ze  wyraznie regularne genruje poczatek slowa w konkatenacji
get⊕r₁ : {r₁ r₂ : RegExp}{w₁ w₂ : Word {Alphabet}} → ⨁Cont r₁ r₂ w₁ w₂ → w₁ ∈ r₁
get⊕r₁ (get⨁Cont ∈₁ _) = ∈₁

-- Funkcja zwracajaca dowod, ze wyraznie regularne genruje koniec slowa w konkatenacji
get⊕r₂ : {r₁ r₂ : RegExp}{s₁ s₂ : Word{Alphabet}} → ⨁Cont r₁ r₂ s₁ s₂ → s₂ ∈ r₂
get⊕r₂ (get⨁Cont _ ∈₂) = ∈₂

-- Funkcja zwracajaca dowod, ze wyrzenie regularne r generuje poczatek slowa
get*r₁ : {r : RegExp}{s₁ s₂ :  Word{Alphabet}} → *Cont r s₁ s₂ → s₁ ∈ r
get*r₁ (get*Cont _ _ _ ∈₁ ∈₂) = ∈₁

-- Funkcja zwracajaca dowod, ze wyrzenie regularne r* generuje koniec slowa
get*r₂ : {r : RegExp}{s₁ s₂ :  Word{Alphabet}} → *Cont r s₁ s₂ → s₂ ∈ (r *)
get*r₂ (get*Cont _ _ _ ∈₁ ∈₂) = ∈₂

-- Funkcja zwracająca dowód, że jeśli z w ∈ r₁ wynika fałsz i z w ∈ r₂ wynika fałsz to z w ∈ (r₁ + r₂) wynika fałsz 
⊻ : {r₁ r₂ : RegExp} → {w : Word {Alphabet}} → (w ∈ r₁ → ⊥) → (w ∈ r₂ → ⊥) → w ∈ (r₁ + r₂) → ⊥
⊻ l r (∈+ˡ w) = l w
⊻ l r (∈+ʳ w) = r w

-- Funkcja decydujaca o przynaleznosci danego slowa do jezyka generowanego przez dane wyrazenie regularne
_∈?_ : (w : Word {Alphabet}) → (r : RegExp) → Dec (w ∈ r)

-- Jeszcze troche funkcji pomocniczych
-- Funkcja decydujaca o tym czy slowo o danym podziale nalezy do jezyka generowanego przez konkatenacje danych wyrazen regularnych
dec⊕ : (r₁ r₂ : RegExp)(s s₁ s₂ : Word {Alphabet})(sp : Split s s₁ s₂) → Dec (⨁Cont r₁ r₂ s₁ s₂)    
dec⊕ r₁ r₂ s s₁ s₂ sp with s₁ ∈? r₁ | s₂ ∈? r₂
...| yes p | yes p₁ = yes (get⨁Cont p p₁)
...| yes p | no ¬p = no (λ p → ¬p (get⊕r₂ p))
...| no ¬p | yes p = no (λ p → ¬p (get⊕r₁ p))
...| no ¬p | no ¬p₁ = no (λ p → ¬p (get⊕r₁ p))

-- Funkcja decydujaca o tym czy slowo o zadanym podziale nalezy do jezyka generowanego przez gwiazde Kleenego danego wyrazenia regularnego 
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

w ∈? (r₁ ⊕ r₂) with ∈?Split w (dec⊕ r₁ r₂ w)
...| yes (∃ w₁ w₂ sp (get⨁Cont x x₁)) = yes (∈⊕ {w} {w₁} {w₂} {r₁} {r₂} sp x x₁)
...| no p = no getNoConcat
  where getNoConcat : w ∈ (r₁ ⊕ r₂) → ⊥
        getNoConcat (∈⊕ {w} {w₁} {w₂} {r₁} {r₂} x p₁ p₂) = p (∃ w₁ w₂ x (get⨁Cont p₁ p₂))
  
ε ∈? (r *) = yes ∈*₁
(x ∷ w) ∈? (r *) with ∈?Split (x ∷ w) (dec* r (x ∷ w))
...| yes (∃ .(l ∷ w₁) s₂ sp (get*Cont l w₁ .s₂ x₁ x₂)) = yes (∈*₂ (∈⊕ sp x₁ x₂))
...| no ¬p = no contra
  where contra : (x ∷ w) ∈ (r *) → ⊥
        contra (∈*₂ (∈⊕ (null .(x ∷ w)) ε∈r xw∈r*)) = contra xw∈r*
        contra (∈*₂ {x ∷ w} {r} (∈⊕ (cont .x .w sp) xw∈r w2∈r*)) = ¬p (∃ (x ∷ _) _ (cont x w sp) (get*Cont x _ _ xw∈r w2∈r*))
 