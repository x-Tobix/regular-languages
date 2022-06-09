module Iso where

import Equality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Naturals using (ℕ; zero; suc; _+_;Bin;⟨⟩;_O;_I;inc) renaming (to to toBin; from to fromBin)
open import Ind using (+-comm)

_∘_ : ∀ {A B C : Set}
  → (B → C)
  → (A → B)
  → (A → C)

(g ∘ f) x = g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +' n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)


equal : _+'_ ≡ _+_
equal = extensionality (λ m → (extensionality (λ n → (same-app m n ))))

data B : Set where
  const : ∀
          (n : ℕ)
          (m : ℕ)
         → B

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record { to = λ x → x ; from = λ x → x ; from∘to = λ x → refl ; to∘from = λ y → refl }

≃-sym : ∀ {A B : Set}
  → A ≃ B
  → B ≃ A

≃-sym A≃B = record { to = from A≃B ; from = to A≃B ; from∘to = to∘from A≃B ; to∘from = from∘to A≃B }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
  → A ≃ C

≃-trans A≃B B≃C = record
  { to = to B≃C ∘ to A≃B
  ; from = from A≃B ∘ from B≃C
  ; from∘to = λ x →
    begin
      from A≃B (from B≃C (to B≃C (to A≃B x)))
    ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
      (from A≃B) (to A≃B x)
    ≡⟨ from∘to A≃B x ⟩
      x
    ∎
  ; to∘from = λ y →
    begin
      to B≃C (to A≃B (from A≃B (from B≃C y)))
    ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
       (to B≃C) (from B≃C y)
    ≡⟨ to∘from B≃C y  ⟩
      y
    ∎
  }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl }

≲-trans : ∀ {A B C : Set}
    → A ≲ B
    → B ≲ C
    → A ≲ C
≲-trans A≲B B≲C = record
  { to = to B≲C ∘ to A≲B
  ; from = from A≲B ∘ from B≲C
  ; from∘to = λ x →
    begin
      from A≲B (from B≲C (to B≲C (to A≲B x)))
    ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
      (from A≲B) (to A≲B x)
    ≡⟨ from∘to A≲B x ⟩
      x
    ∎
  }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B

≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
  → A ≲ B

≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = λ x → from∘to A≃B x }


record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record { to = λ z → z ; from = λ x → x }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
  → B ⇔ A

⇔-sym A⇔B = record { to = from A⇔B ; from = to A⇔B }


⇔-trans : ∀ {A B C : Set}
    → A ⇔ B
    → B ⇔ C
    → A ⇔ C
⇔-trans A⇔B B⇔C = record { to = λ x → to B⇔C (to A⇔B x) ; from = λ z → from A⇔B (from B⇔C z) }
