{-# OPTIONS --allow-unsolved-metas #-}
module Negation where

open import Equality using (_≡_; refl)
open import Naturals using (ℕ; zero; suc)
open import Rels using (_<_; z<s; s<s)
open import Conns using (_×_; _⊎_; in₁; in₂; ⊥; ⊥-elim; ⟨_,_⟩; case-⊎)
open import Iso using (_≃_; extensionality; _≲_; _⇔_; _∘_)
open Conns._×_

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to = λ { ⟨ in₁ a , c ⟩ → in₁ ⟨ a , c ⟩ ; ⟨ in₂ b , c ⟩ → in₂ ⟨ b , c ⟩}
  ; from = λ{ (in₁ ⟨ a , c ⟩ ) → ⟨ in₁ a , c ⟩ ; (in₂ ⟨ b , c ⟩ ) → ⟨ in₂ b , c ⟩}
  ; from∘to = λ{ ⟨ in₁ a , c ⟩ → refl ; ⟨ in₂ b , c ⟩ → refl}
  ; to∘from = λ{ (in₁ ⟨ a , c ⟩ ) → refl ; (in₂ ⟨ b , c ⟩ ) → refl}
  }

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim = λ na a → na a

¬¬-intro' : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro' a = λ na → na a

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition a→b = λ nb a → nb (a→b a)

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ =  extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀ {n : ℕ} → ¬ n < n
<-irreflexive (s<s n<n) = <-irreflexive n<n

⊎-dual-× : ∀ { A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record
  { to = λ{ f → ⟨ (λ a → f (in₁ a)) , (λ b → f (in₂ b)) ⟩ }
  ; from = λ { ⟨ na , nb ⟩ (in₁ a) → na a
             ; ⟨ na , nb ⟩ (in₂ b) → nb b}
  ; from∘to = λ { f → {!!}}
  ; to∘from = λ {⟨ na , nb ⟩ → refl}
  }

⊎-dual-×' : ∀ { A B : Set} → (¬ A) ⊎ (¬ B) ≃ ¬ (A × B)
⊎-dual-×' = record
  { to = λ { (in₁ na) ⟨ a , b ⟩ → na a 
           ; (in₂ nb) ⟨ a , b ⟩ → nb b}
  ; from = λ {x → {!!}}
  ; from∘to = λ x → {!!}
  ; to∘from = λ y → {!!}
  }

--em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
--em-irrefutable = {!   !}

--postulate
   --Excluded-Middle : ∀ {A : Set} → A ⊎ ¬ A
   -- Double-Negation-Elimination : ∀ {A : Set} → ¬ ¬ A → A
   -- Peirce’s-Law : ∀ {A B : Set} → ((A → B) → A) → A
   -- Implication-as-disjunction : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
   -- De-Morgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
