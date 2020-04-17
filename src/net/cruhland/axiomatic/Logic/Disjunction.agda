module net.cruhland.axiomatic.Logic.Disjunction where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Disjunction (_∨_ : Set → Set → Set) : Set₁ where
  field
    ∨-introᴸ : {A B : Set} → A → A ∨ B
    ∨-introᴿ : {A B : Set} → B → A ∨ B
    ∨-elim : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C

    ∨-βᴸ :
      ∀ {A B C} {f : A → C} {g : B → C} {a : A} → ∨-elim f g (∨-introᴸ a) ≡ f a
    ∨-βᴿ :
      ∀ {A B C} {f : A → C} {g : B → C} {b : B} → ∨-elim f g (∨-introᴿ b) ≡ g b

    ∨-η : ∀ {A B} {a∨b : A ∨ B} → ∨-elim ∨-introᴸ ∨-introᴿ a∨b ≡ a∨b
