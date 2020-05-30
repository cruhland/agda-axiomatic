module net.cruhland.axiomatic.Logic.Falsity where

open import Level using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

record Falsity (⊥ : Set) : Setω where
  field
    -- No ⊥-intro rules; ⊥ is empty
    ⊥-elim : ∀ {α} {A : Set α} → ⊥ → A

    -- No ⊥-β rules

    -- No ⊥-η rules

  ¬_ : ∀ {α} → Set α → Set α
  ¬ A = A → ⊥

  ¬sym : {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
  ¬sym x≢y = λ y≡x → x≢y (sym y≡x)
