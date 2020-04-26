module net.cruhland.axiomatic.Logic.Disjunction where

open import Function using (const; id)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Disjunction (_∨_ : Set → Set → Set) : Set₁ where
  field
    ∨-introᴸ : {A B : Set} → A → A ∨ B
    ∨-introᴿ : {A B : Set} → B → A ∨ B

    ∨-elim :
      {A B : Set} (C : A ∨ B → Set) →
      ((a : A) → C (∨-introᴸ a)) →
      ((b : B) → C (∨-introᴿ b)) →
      ∀ a∨b →
      C a∨b

    ∨-βᴸ :
      ∀ {A B} {C : A ∨ B → Set}
      {f : (a : A) → C (∨-introᴸ a)} {g : (b : B) → C (∨-introᴿ b)} {a : A} →
      ∨-elim C f g (∨-introᴸ a) ≡ f a

    ∨-βᴿ :
      ∀ {A B} {C : A ∨ B → Set}
      {f : (a : A) → C (∨-introᴸ a)} {g : (b : B) → C (∨-introᴿ b)} {b : B} →
      ∨-elim C f g (∨-introᴿ b) ≡ g b

    ∨-η :
      ∀ {A B} {a∨b : A ∨ B} →
      ∨-elim (const (A ∨ B)) ∨-introᴸ ∨-introᴿ a∨b ≡ a∨b

  ∨-rec : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
  ∨-rec {A} {B} {C} f g a∨b = ∨-elim (const C) f g a∨b

  ∨-rec-βᴸ :
    ∀ {A B C} {f : A → C} {g : B → C} {a : A} → ∨-rec f g (∨-introᴸ a) ≡ f a
  ∨-rec-βᴸ = ∨-βᴸ

  ∨-rec-βᴿ :
    ∀ {A B C} {f : A → C} {g : B → C} {b : B} → ∨-rec f g (∨-introᴿ b) ≡ g b
  ∨-rec-βᴿ = ∨-βᴿ

  ∨-recᴸ : ∀ {A B} → (B → A) → A ∨ B → A
  ∨-recᴸ g = ∨-rec id g

  ∨-recᴿ : ∀ {A B} → (A → B) → A ∨ B → B
  ∨-recᴿ f = ∨-rec f id

  ∨-comm : ∀ {A B} → A ∨ B → B ∨ A
  ∨-comm A∨B = ∨-rec ∨-introᴿ ∨-introᴸ A∨B
