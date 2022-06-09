{-# OPTIONS --allow-unsolved-metas #-}

module Decidable where

import Equality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Naturals using (ℕ; zero; suc)
open import Conns using (_×_; _⊎_; in₁; in₂; ⊥; ⊥-elim; ⟨_,_⟩; case-⊎; ⊤; tt)
open import Negation using (¬_; ¬¬-intro')
open import Rels using (_<_; z<s; s<s; _≤_; z≤n; s≤s; ≤-refl; ≤-trans; +-monoʳ-≤)
open import Iso using (_≃_; extensionality; _≲_; _⇔_; _∘_)
open Iso._⇔_

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true x = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n x = z≤n
≤ᵇ→≤ (suc m) (suc n) x = s≤s (≤ᵇ→≤ m n x)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z = λ ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n 

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no (λ ())
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no λ { (s≤s m≤n) → ¬m≤n m≤n}

-- Praca domowa: zdefiniować _<?_

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

not : Bool → Bool
not true  = false
not false = true

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×-dec yes b = yes ⟨ a , b ⟩
yes _ ×-dec no ¬b  = no λ { ⟨ A , B ⟩ → ¬b B}
no ¬a ×-dec _ = no λ { ⟨ A , B ⟩ → ¬a A}

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes a ⊎-dec b = yes (in₁ a)
no a ⊎-dec yes b = yes (in₂ b)
no na ⊎-dec no nb = no λ { (in₁ a) → na a ; (in₂ b) → nb b}

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes a) = no (¬¬-intro' a)
¬? (no a) = yes a

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
x →-dec y = {!   !}

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes _) (yes _) = refl
∧-× (yes _) (no _) = refl
∧-× (no _) _ = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ x y = {!   !}

⊃-→ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ⊃ ⌊ y ⌋ ≡ ⌊ x →-dec y ⌋
⊃-→ x y = {!   !}

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ x = {!   !}

{- toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m) -}
