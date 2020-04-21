module net.cruhland.axiomatic.Logic.Falsity where

open import Relation.Binary.PropositionalEquality using (_≡_; sym)

record Falsity (⊥ : Set) : Set₁ where
  field
    -- No ⊥-intro rules; ⊥ is empty
    ⊥-elim : {A : Set} → ⊥ → A

    -- No ⊥-β rules

    -- No ⊥-η rules

  ¬_ : Set → Set
  ¬ A = A → ⊥

  ¬sym : {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
  ¬sym x≢y = λ y≡x → x≢y (sym y≡x)
