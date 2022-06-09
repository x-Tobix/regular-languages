module Conns where


import Equality as Eq
open Eq using (_≡_; refl;cong)
open Eq.≡-Reasoning
open import Naturals using (ℕ; zero;  suc; _∙_; _+_)
open import Iso using (_∘_;_≃_; extensionality)
open Iso.≃-Reasoning


------------------------------------
-- produkt kartezjański jako koniunkcja
------------------------------------

record _×_ ( A B : Set ) : Set where
 constructor ⟨_,_⟩
 field
    proj₁ : A
    proj₂ : B
open _×_

infixr 2 _×_

-- przemienność produktu z dokładnością do izomorfizmu
×-comm : ∀ { A B : Set } → A × B ≃ B × A
×-comm =
  record
  { to = λ{ ⟨ x , y ⟩ →  ⟨ y , x ⟩ }
  ; from = λ{ ⟨ x , y ⟩ →  ⟨ y , x ⟩ }
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

-- łączność produktu z dokładnością do izomorfizmu
×-assoc : ∀ { A B C : Set }  → A × ( B × C ) ≃ ( A × B ) × C
×-assoc =
  record
    { to      = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from    = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from∘to = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    ; to∘from = λ{ ⟨ ⟨ x ,  y ⟩ , z  ⟩ → refl }
    }

-----------------------------------
---- prawda jako typ z jednym bezparametrycznym konstruktorem
-----------------------------------
data ⊤' : Set where
  tt' : ⊤'

record ⊤ : Set where
  constructor tt

open ⊤

-- i twierdzenie
⊤-identityₗ : ∀ { A : Set } → ⊤ × A ≃ A
⊤-identityₗ =
  record
  { to =  λ { ⟨ tt , x ⟩ → x }
  ; from =  λ x → ⟨ tt , x ⟩
  ; from∘to = λ{ ⟨ tt , y ⟩ → refl}
  ; to∘from = λ y → refl
  }

⊤-identityᵣ : ∀ { A : Set } → A × ⊤ ≃ A
⊤-identityᵣ =
  record
  { to = λ {⟨ A , T ⟩ → A}
  ; from = λ A → ⟨ A , tt ⟩
  ; from∘to = λ {⟨ A , T ⟩ → refl}
  ; to∘from = λ A → refl
  }

----------------------------------
-- alternatywa jako suma rozdzielna
-----------------------------------
-----------------------------------
data _⊎_ ( A B : Set ) : Set where
  in₁ : A → A ⊎ B
  in₂ : B → A ⊎ B


case-⊎ : ∀ { A B C : Set }
  → ( A → C )
  → ( B → C )
 ------------
  → ( A ⊎ B → C )
case-⊎ f g (in₁ x) =  f x
case-⊎ f g (in₂ x) =  g x 

----------------------------------
-- implikacja jako funkcja
----------------------------------
→-elim : ∀ { A B : Set }
  → ( A → B )
  → A
  ---
  → B
→-elim = λ z → z

currying : ∀ { A B C : Set } → ( A → ( B → C ) ) ≃ ( A × B  → C )
currying =
  record
    { to = λ {f ⟨ a , b ⟩ → f a b}
    ; from = λ {f a b →  f ⟨ a , b ⟩}
    ; from∘to = λ f → refl
    ; to∘from = λ f → refl
    }

--
-- inne własności implikacji
--

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎  =
  record
    { to = λ {x → ⟨ (λ y → x (in₁ y)) , (λ z → x (in₂ z)) ⟩}
    ; from = λ { ⟨ x , y ⟩ (in₁ z) → x z ;
                 ⟨ x , y ⟩ (in₂ z) → y z}
    ; from∘to = λ x → extensionality λ { (in₁ x) → refl ; (in₂ x) → refl}
    ; to∘from = λ {⟨ x , y ⟩ → refl}
    }

---------------------------------
-- fałsz jako typ danych bez konstruktorów
---------------------------------
data ⊥ : Set where


-- eliminacja fałszu (aka z fałszu wynika wszystko)
⊥-elim : ∀ { A : Set } → ⊥ → A
⊥-elim ()


-------------------------------------------
-------------------------------------------

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_


---- podstawowe własności

¬-elim : ∀ { A : Set } → A → ¬ A → ⊥
¬-elim x f = f x



¬¬-intro : ∀ { A : Set } → A → ¬ ¬ A
--¬¬-intro : ∀ { A : Set } → A → (¬ A → ⊥)
¬¬-intro x = ¬-elim x

-----------------------------------------
-- UWAGA
-- --------------------------------------
-- nie jesteśmy w stanie zdefiniować funkcji typu
-- ∀ { A : Set } → ¬ ¬ A → A ale:
--
elim₁ : ∀ {A : Set } { x : A } → ¬ ¬ A → A
elim₁ {A} {x} = λ _ → x
--
elim₂ : ¬ ¬ ⊥ → ⊥
elim₂ = λ x → x (λ z → z)

-- ale:
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

-- prawo kontrapozycji:
contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)


-------------------------------------------
-------------------------------------------
--- nierównanie
--- ----------------------------------------
---
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {n : ℕ} → 0 ≢ suc n
peano = λ ()

-- i w koncu

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

--------------------------------------
------------Kwantyfikatory------------
--------------------------------------

∀-elim : ∀ {A : Set} (B : A → Set)
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim = λ B L → L


data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B


∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , m ⟩ = f x m

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ}
        → odd n
        → even(suc n)

data odd where
  suc : ∀ {n : ℕ}
       → even n
       → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ](m ∙ 2 ≡ n)
odd-∃ : ∀ {n : ℕ} → odd n → ∃[ m ](1 + m ∙ 2 ≡ n)

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc x) with odd-∃ x
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (suc x) with even-∃ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩
