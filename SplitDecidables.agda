module SplitDecidables where
  open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
  open import Decidable using (Dec ; no ; yes)
  open import Split
  open import Conns using (⊥)

  -- Służy do trzymania przenośnej funkcji która dla słowa zwraca funkcję przyjmującą dwa słowa i splita składającego się z tych słów
  GetSplitMorphismFromWords : Word {Alphabet} → Set₁
  GetSplitMorphismFromWords w = (w₁ w₂ : Word {Alphabet}) → Split w w₁ w₂ → Set

  -- Dostajemy decidable dla istnienia splitu danych słow w słowie wyjściowym
  GetSplitDecidable : {w : Word {Alphabet}} → GetSplitMorphismFromWords w → Set
  GetSplitDecidable {w} Morphism = (w₁ w₂ : Word {Alphabet}) -> (sp : Split w w₁ w₂) → Dec (Morphism w₁ w₂ sp)

  -- Obiekt decydujący czy dane słowa tworzą splita
  data ∈Split (w : Word {Alphabet})(Morphism : GetSplitMorphismFromWords w) : Set where
    ∃ : (w₁ w₂ : Word {Alphabet}) → (sp : Split w w₁ w₂) → Morphism w₁ w₂ sp → ∈Split w Morphism

  -- Mówi nam o tym czy dane słowo ma splita          
  ∈?Split : (w : Word {Alphabet}) → {P : GetSplitMorphismFromWords w} → (GetSplitDecidable P) → Dec (∈Split w P)
  ∈?Split ε getSD with getSD ε ε (null ε)
  ...| yes p = yes (∃ ε ε (null ε) p)
  ...| no p = no getNoSplit
    where getNoSplit : ∈Split ε _ → ⊥
          getNoSplit (∃ ε ε (null ε) x) = p x
  ∈?Split (x ∷ w) getSD with ∈?Split w (GetDecidableForNoFirstElementMorphism x getSD) | getSD _ _ (null (x ∷ w))
    where GetNoFirstElementMorphism : (w : Word {Alphabet}) → (l : Alphabet) → GetSplitMorphismFromWords (l ∷ w) → GetSplitMorphismFromWords w
          GetNoFirstElementMorphism w l P w₁ w₂ sp = P (l ∷ w₁) w₂ (cont l w sp)
          GetDecidableForNoFirstElementMorphism : {w : Word {Alphabet}} → (l : Alphabet) → {P : GetSplitMorphismFromWords (l ∷ w)} → (GetSplitDecidable P) → (GetSplitDecidable (GetNoFirstElementMorphism w l P))
          GetDecidableForNoFirstElementMorphism l dec w₁ w₂ sp = dec (l ∷ w₁) w₂ (cont l _ sp)
  ...| yes _ | yes p = yes (∃ ε (x ∷ w) (null (x ∷ w)) p)
  ...| yes (∃ w₁ w₂ sp x₁) | no _ = yes (∃ (x ∷ w₁) w₂ (cont x w sp) x₁)
  ...| no _ | yes p = yes (∃ ε (x ∷ w) (null (x ∷ w)) p)
  ...| no p₁ | no p₂ = no getNoSplit
    where getNoSplit : ∈Split (x ∷ w) _ → ⊥
          getNoSplit (∃ ε (x ∷ w) (null _) x₁) = p₂ x₁
          getNoSplit (∃ (x ∷ w₁) w₂ (cont x w sp) x₁) = p₁ (∃ w₁ w₂ sp x₁)
