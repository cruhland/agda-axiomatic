module net.cruhland.axiomatic.Logic.Conjunction where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Conjunction (_∧_ : Set → Set → Set) : Set₁ where
  field
    ∧-intro : {A B : Set} → A → B → A ∧ B
    ∧-elimᴸ : {A B : Set} → A ∧ B → A
    ∧-elimᴿ : {A B : Set} → A ∧ B → B

    ∧-βᴸ : ∀ {A B} {a : A} {b : B} → ∧-elimᴸ (∧-intro a b) ≡ a
    ∧-βᴿ : ∀ {A B} {a : A} {b : B} → ∧-elimᴿ (∧-intro a b) ≡ b

    ∧-η : ∀ {A B} {a∧b : A ∧ B} → ∧-intro (∧-elimᴸ a∧b) (∧-elimᴿ a∧b) ≡ a∧b

  ∧-comm : ∀ {A B} → A ∧ B → B ∧ A
  ∧-comm A∧B = ∧-intro (∧-elimᴿ A∧B) (∧-elimᴸ A∧B)
