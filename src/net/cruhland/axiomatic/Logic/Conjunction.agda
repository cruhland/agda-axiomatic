module net.cruhland.axiomatic.Logic.Conjunction where

open import Level using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Conjunction (_∧_ : ∀ {α β} → Set α → Set β → Set) : Setω where
  field
    ∧-intro : ∀ {α β} {A : Set α} {B : Set β} → A → B → A ∧ B
    ∧-elimᴸ : ∀ {α β} {A : Set α} {B : Set β} → A ∧ B → A
    ∧-elimᴿ : ∀ {α β} {A : Set α} {B : Set β} → A ∧ B → B

    ∧-βᴸ :
      ∀ {α β} {A : Set α} {B : Set β} {a : A} {b : B} →
      ∧-elimᴸ (∧-intro a b) ≡ a
    ∧-βᴿ :
      ∀ {α β} {A : Set α} {B : Set β} {a : A} {b : B} →
      ∧-elimᴿ (∧-intro a b) ≡ b

    ∧-η :
      ∀ {α β} {A : Set α} {B : Set β} {a∧b : A ∧ B} →
      ∧-intro (∧-elimᴸ a∧b) (∧-elimᴿ a∧b) ≡ a∧b

  ∧-comm : ∀ {α β} {A : Set α} {B : Set β} → A ∧ B → B ∧ A
  ∧-comm A∧B = ∧-intro (∧-elimᴿ A∧B) (∧-elimᴸ A∧B)
