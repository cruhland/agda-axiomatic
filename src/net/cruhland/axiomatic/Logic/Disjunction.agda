module net.cruhland.axiomatic.Logic.Disjunction where

open import Function using (const; id; _∘_)
open import Level using (_⊔_; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Disjunction (_∨_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)) : Setω where
  field
    ∨-introᴸ : ∀ {α β} {A : Set α} {B : Set β} → A → A ∨ B
    ∨-introᴿ : ∀ {α β} {A : Set α} {B : Set β} → B → A ∨ B

    ∨-elim :
      ∀ {α β χ} {A : Set α} {B : Set β} (C : A ∨ B → Set χ) →
      ((a : A) → C (∨-introᴸ a)) →
      ((b : B) → C (∨-introᴿ b)) →
      ∀ a∨b →
      C a∨b

    ∨-βᴸ :
      ∀ {α β χ} {A : Set α} {B : Set β} {C : A ∨ B → Set χ}
      {f : (a : A) → C (∨-introᴸ a)} {g : (b : B) → C (∨-introᴿ b)} {a : A} →
      ∨-elim C f g (∨-introᴸ a) ≡ f a

    ∨-βᴿ :
      ∀ {α β χ} {A : Set α} {B : Set β} {C : A ∨ B → Set χ}
      {f : (a : A) → C (∨-introᴸ a)} {g : (b : B) → C (∨-introᴿ b)} {b : B} →
      ∨-elim C f g (∨-introᴿ b) ≡ g b

    ∨-η :
      ∀ {α β} {A : Set α} {B : Set β} {a∨b : A ∨ B} →
      ∨-elim (const (A ∨ B)) ∨-introᴸ ∨-introᴿ a∨b ≡ a∨b

  ∨-rec :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} →
    (A → C) → (B → C) → A ∨ B → C
  ∨-rec {C = C} f g a∨b = ∨-elim (const C) f g a∨b

  ∨-rec-βᴸ :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ}
    {f : A → C} {g : B → C} {a : A} → ∨-rec f g (∨-introᴸ a) ≡ f a
  ∨-rec-βᴸ = ∨-βᴸ

  ∨-rec-βᴿ :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ}
    {f : A → C} {g : B → C} {b : B} → ∨-rec f g (∨-introᴿ b) ≡ g b
  ∨-rec-βᴿ = ∨-βᴿ

  ∨-recᴸ : ∀ {α β} {A : Set α} {B : Set β} → (B → A) → A ∨ B → A
  ∨-recᴸ g = ∨-rec id g

  ∨-recᴿ : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → A ∨ B → B
  ∨-recᴿ f = ∨-rec f id

  ∨-comm : ∀ {α β} {A : Set α} {B : Set β} → A ∨ B → B ∨ A
  ∨-comm A∨B = ∨-rec ∨-introᴿ ∨-introᴸ A∨B

  ∨-mapᴸ :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (A → C) → A ∨ B → C ∨ B
  ∨-mapᴸ f A∨B = ∨-rec (∨-introᴸ ∘ f) ∨-introᴿ A∨B

  ∨-mapᴿ :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (B → C) → A ∨ B → A ∨ C
  ∨-mapᴿ g A∨B = ∨-rec ∨-introᴸ (∨-introᴿ ∘ g) A∨B

  ∨-merge : ∀ {α} {A : Set α} → A ∨ A → A
  ∨-merge = ∨-rec id id
