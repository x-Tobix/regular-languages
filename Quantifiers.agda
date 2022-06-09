module Quantifiers where

open import Equality using (_≡_; refl; cong)
open import Naturals using (ℕ; zero; suc; _+_; _∙_)
open import Rels using (_<_; z<s; s<s; _≤_; z≤n; s≤s; ≤-refl; ≤-trans)
open import Conns using (_×_; _⊎_; in₁; in₂; ⊥; ⊥-elim; ⟨_,_⟩; case-⊎; ¬_)
open import Iso using (_≃_; extensionality; _≲_; _⇔_; _∘_)
open import Ind using (+-comm; +-suc)
open Conns._×_

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ f → ⟨ (λ a → proj₁ (f a) ) , (λ a → proj₂ (f a)) ⟩
  ; from = λ { ⟨ Bx , Cx ⟩ a → ⟨ Bx a , Cx a ⟩}
  ; from∘to = λ f → refl
  ; to∘from = λ { ⟨ Bx , Cx ⟩  → refl}
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → 
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ = λ { (in₁ Bx) a → in₁ (Bx a)
                   ; (in₂ Cx) a → in₂ (Cx a)}

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
infix 2 ∃-syntax

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
              { to = λ { ⟨ a , in₁ Ba ⟩ → in₁ ⟨ a , Ba ⟩
                       ; ⟨ a , in₂ Ca ⟩ → in₂ ⟨ a , Ca ⟩}
              ; from = λ { (in₁ ⟨ a , Ba ⟩) → ⟨ a , in₁ Ba ⟩
                         ; (in₂ ⟨ a , Ca ⟩) → ⟨ a , in₂ Ca ⟩}
              ; from∘to = λ { ⟨ a , in₁ Ba ⟩ → refl
                            ; ⟨ a , in₂ Ca ⟩ → refl}
              ; to∘from = λ { (in₁ ⟨ a , Ba ⟩) → refl
                            ; (in₂ ⟨ a , Ca ⟩) → refl}
              }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = λ { ⟨ a , ⟨ Ba , Ca ⟩ ⟩ → ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩}

≤-refl-suc : ∀ (n : ℕ) → n ≤ suc n
≤-refl-suc zero = z≤n
≤-refl-suc (suc n) = s≤s (≤-refl-suc n)

+-implies-≤ : ∀ {x y z : ℕ} → x + y ≡ z → y ≤ z
+-implies-≤ {zero} {y} {y} refl = ≤-refl {y}
+-implies-≤ {suc x} {y} {suc z} refl with +-implies-≤ {x} {y} {z} refl
... | y≤z  =  ≤-trans y≤z (≤-refl-suc z)

∃-implies-≤ : ∀ {y z : ℕ} → (∃[ x ] (x + y ≡ z)) → (y ≤ z)
∃-implies-≤ {y} {z} ⟨ x , p ⟩ = (+-implies-≤ {x} {y} {z} p)

≤-implies-∃ : ∀ {y z : ℕ} → ((y ≤ z) → (∃[ x ] (x + y ≡ z)))
≤-implies-∃ {y} {z} z≤n = ⟨ z , +-comm z zero ⟩
≤-implies-∃ (s≤s {m} {n} m≤n) with ≤-implies-∃ m≤n
... | ⟨ x , refl ⟩ = ⟨ x , +-suc x m ⟩

∃⇔≤ : ∀ {y z : ℕ} → ((y ≤ z) ⇔ (∃[ x ] (x + y ≡ z)))
∃⇔≤ = record { to = ≤-implies-∃ ; from = ∃-implies-≤ }



¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ (∃[ x ] B x)) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , nBa ⟩ f = nBa (f a)
