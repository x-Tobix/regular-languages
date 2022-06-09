module List_lab where

import Equality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Naturals using (ℕ; zero; suc; _+_; _∙_)
open import Rels using (_≤_; s≤s; z≤n)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎

++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys rewrite length-++ xs ys = refl

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ (x ∷ [] )

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
    → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite reverse-++-distrib xs ys | ++-assoc (reverse ys) (reverse xs) (x ∷ []) = refl

reverse-involutive : ∀ {A : Set} (xs : List A)
 → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) (x ∷ []) | reverse-involutive xs = refl

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
    → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum =  foldr _+_ 0  

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = (Any (_≡ x) xs)
