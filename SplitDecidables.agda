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

  -- Obiekt decydujący 
  data HasSplit (w : Word {Alphabet})(Morphism : GetSplitMorphismFromWords w) : Set where
    exists : (w₁ w₂ : Word {Alphabet}) → (sp : Split w w₁ w₂) → Morphism w₁ w₂ sp → HasSplit w Morphism
           
  decHasSplit : (s : Word {Alphabet}){P : GetSplitMorphismFromWords s} → (GetSplitDecidable P) → Dec (HasSplit s P)
  decHasSplit ε decP with decP ε ε (null ε)
  decHasSplit ε decP | yes p = yes (exists ε ε (null ε) p)
  decHasSplit ε decP | no ¬p = no contra
    where contra : HasSplit ε _ → ⊥
          contra (exists .ε .ε (null .ε) x) = ¬p x
  decHasSplit (x ∷ s) decP with decHasSplit s (shiftOverDec x decP) | decP _ _ (null (x ∷ s))
    where ShiftOver : (s : Word {Alphabet})(c : Alphabet) → GetSplitMorphismFromWords (c ∷ s) → GetSplitMorphismFromWords s
          ShiftOver s c P s₁ s₂ sp = P (c ∷ s₁) s₂ (cont c s sp)
          shiftOverDec : {s : Word {Alphabet}}(c : Alphabet){P : GetSplitMorphismFromWords (c ∷ s)} → (GetSplitDecidable P) → (GetSplitDecidable (ShiftOver s c P))
          shiftOverDec c dec s₁ s₂ sp = dec (c ∷ s₁) s₂ (cont c _ sp)
  decHasSplit (x ∷ s) decP | yes p | yes p₁ = yes (exists ε (x ∷ s) (null (x ∷ s)) p₁)
  decHasSplit (x ∷ s) decP | yes (exists s₁ s₂ sp x₁) | no ¬p = yes (exists (x ∷ s₁) s₂ (cont x s sp) x₁)
  decHasSplit (x ∷ s) decP | no ¬p | yes p = yes (exists ε (x ∷ s) (null (x ∷ s)) p)
  decHasSplit (x ∷ s) decP | no ¬p | no ¬p₁ = no contra
    where contra : HasSplit (x ∷ s) _ → ⊥
          contra (exists .ε .(x ∷ s) (null ._) x₁) = ¬p₁ x₁
          contra (exists (.x ∷ s₁) s₂ (cont .x .s sp) x₁) = ¬p (exists s₁ s₂ sp x₁)
