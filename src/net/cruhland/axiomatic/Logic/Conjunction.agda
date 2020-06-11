module net.cruhland.axiomatic.Logic.Conjunction where

open import Function using (id)
open import Level using (_⊔_; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Conjunction (_∧_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)) : Setω where
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

  ∧-map :
    ∀ {α β χ δ} {A : Set α} {B : Set β} {C : Set χ} {D : Set δ} →
    (A → C) → (B → D) → A ∧ B → C ∧ D
  ∧-map f g a∧b = ∧-intro (f (∧-elimᴸ a∧b)) (g (∧-elimᴿ a∧b))

  ∧-mapᴸ :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (A → C) → A ∧ B → C ∧ B
  ∧-mapᴸ f a∧b = ∧-map f id a∧b

  ∧-mapᴿ :
    ∀ {α β δ} {A : Set α} {B : Set β} {D : Set δ} → (B → D) → A ∧ B → A ∧ D
  ∧-mapᴿ g a∧b = ∧-map id g a∧b
