module Equals2 where

import Equality as Eq
open Eq using (_≡_; refl; cong; subst)
open import Naturals using (ℕ; zero; suc; _+_)

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x

refl-≐ {A} {x} P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
  → x ≐ z

trans-≐ {A} {x} {y} {z} r1 r2 P Px = r2 P (r1 P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
  → y ≐ x

sym-≐ {A} {x} {y} r P Py = (r Q id_Px) Py
  where
    Q : A → Set
    Q z = P z → P x
    id_Px : P x → P x
    id_Px px = px

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
  → x ≐ y

≡-implies-≐ {A} {x} {y} x≡y P Px = subst P x≡y Px
