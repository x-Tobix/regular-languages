module SplitDecidables where
  open import Alphabet using (Alphabet; a ; b; Word; ε; _∷_ ; _++_)
  open import Decidable using (Dec ; no ; yes)
  open import Split
  open import Conns using (⊥)

  SplitProp : Word {Alphabet} → Set₁
  SplitProp s = (s₁ s₂ : Word {Alphabet}) → Split s s₁ s₂ → Set

  SplitDec : {s : Word {Alphabet}} → SplitProp s → Set
  SplitDec {s = s} P = (s₁ s₂ : Word {Alphabet})(sp : Split s s₁ s₂) → Dec (P s₁ s₂ sp)

  data HasSplit (s : Word {Alphabet})(P : SplitProp s) : Set where
    exists : (s₁ s₂ : Word {Alphabet})(sp : Split s s₁ s₂)
           → P s₁ s₂ sp
           → HasSplit s P
           
  decHasSplit : (s : Word {Alphabet}){P : SplitProp s} → (SplitDec P) → Dec (HasSplit s P)
  decHasSplit ε decP with decP ε ε (null ε)
  decHasSplit ε decP | yes p = yes (exists ε ε (null ε) p)
  decHasSplit ε decP | no ¬p = no contra
    where contra : HasSplit ε _ → ⊥
          contra (exists .ε .ε (null .ε) x) = ¬p x
  decHasSplit (x ∷ s) decP with decHasSplit s (shiftOverDec x decP) | decP _ _ (null (x ∷ s))
    where ShiftOver : (s : Word {Alphabet})(c : Alphabet) → SplitProp (c ∷ s) → SplitProp s
          ShiftOver s c P s₁ s₂ sp = P (c ∷ s₁) s₂ (cont c s sp)
          shiftOverDec : {s : Word {Alphabet}}(c : Alphabet){P : SplitProp (c ∷ s)} → (SplitDec P) → (SplitDec (ShiftOver s c P))
          shiftOverDec c dec s₁ s₂ sp = dec (c ∷ s₁) s₂ (cont c _ sp)
  decHasSplit (x ∷ s) decP | yes p | yes p₁ = yes (exists ε (x ∷ s) (null (x ∷ s)) p₁)
  decHasSplit (x ∷ s) decP | yes (exists s₁ s₂ sp x₁) | no ¬p = yes (exists (x ∷ s₁) s₂ (cont x s sp) x₁)
  decHasSplit (x ∷ s) decP | no ¬p | yes p = yes (exists ε (x ∷ s) (null (x ∷ s)) p)
  decHasSplit (x ∷ s) decP | no ¬p | no ¬p₁ = no contra
    where contra : HasSplit (x ∷ s) _ → ⊥
          contra (exists .ε .(x ∷ s) (null ._) x₁) = ¬p₁ x₁
          contra (exists (.x ∷ s₁) s₂ (cont .x .s sp) x₁) = ¬p (exists s₁ s₂ sp x₁)
