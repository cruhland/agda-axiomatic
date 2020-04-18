module net.cruhland.axiomatic.Logic.Falsity where

record Falsity (⊥ : Set) : Set₁ where
  field
    -- No ⊥-intro rules; ⊥ is empty
    ⊥-elim : {A : Set} → ⊥ → A

    -- No ⊥-β rules

    -- No ⊥-η rules

  ¬_ : Set → Set
  ¬ A = A → ⊥
