module net.cruhland.axiomatic.Logic where

open import Function using (id; _∘_)
open import Level using (_⊔_; Setω) renaming (zero to lzero)
open import net.cruhland.axiomatic.Logic.Conjunction as Conjunction
import net.cruhland.axiomatic.Logic.Disjunction as Disjunction
import net.cruhland.axiomatic.Logic.Exists as Exists
import net.cruhland.axiomatic.Logic.Falsity as Falsity
import net.cruhland.axiomatic.Logic.Truth as Truth

record LogicBundle : Setω where
  open Conjunction public
  open Disjunction public
  open Exists public
  open Falsity public
  open Truth public

  ∨-identᴸ : ∀ {α β} {B : Set β} → ⊥̂ {α} ∨ B → B
  ∨-identᴸ = ∨-recᴿ ⊥̂-elim

  ∨-identᴿ : ∀ {α β} {A : Set α} → A ∨ ⊥̂ {β} → A
  ∨-identᴿ = ∨-recᴸ ⊥̂-elim

  ∨-forceᴸ : ∀ {α β} {A : Set α} {B : Set β} → ¬ B → A ∨ B → A
  ∨-forceᴸ ¬b = ∨-identᴿ {β = lzero} ∘ ∨-mapᴿ (⊥-elim ∘ ¬b)

  ∨-forceᴿ : ∀ {α β} {A : Set α} {B : Set β} → ¬ A → A ∨ B → B
  ∨-forceᴿ ¬a = ∨-identᴸ {α = lzero} ∘ ∨-mapᴸ (⊥-elim ∘ ¬a)

  _↔_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
  A ↔ B = (A → B) ∧ (B → A)

  infixl 0 _↔_

  ↔-refl : ∀ {α} {A : Set α} → A ↔ A
  ↔-refl = ∧-intro id id

  ↔-sym : ∀ {α β} {A : Set α} {B : Set β} → A ↔ B → B ↔ A
  ↔-sym A↔B = ∧-comm A↔B

  ↔-trans :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → A ↔ B → B ↔ C → A ↔ C
  ↔-trans A↔B B↔C =
    ∧-intro (∧-elimᴸ B↔C ∘ ∧-elimᴸ A↔B) (∧-elimᴿ A↔B ∘ ∧-elimᴿ B↔C)

  ↔-bimap :
    ∀ {α β χ δ} {A : Set α} {B : Set β} {C : Set χ} {D : Set δ} →
      ((A → B) → (C → D)) → ((B → A) → (D → C)) → A ↔ B → C ↔ D
  ↔-bimap = ∧-map
