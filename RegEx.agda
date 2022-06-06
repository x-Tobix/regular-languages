module RegEx where

data RegExp : Set where
    ∅ : RegExp                      -- Empty set
    ε : RegExp                      -- Empty word
    literal : Alphabet → RegExp     -- literal
    _⋆ : RegExp → RegExp            -- Kleene star
    _⊕_ : RegExp → RegExp            -- Concatenation
    _+_ : RegExp → RegExp             -- Sum
    ⟨_⟩ : RegExp → RegExp            -- Grouping
