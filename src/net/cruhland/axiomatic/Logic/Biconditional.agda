module net.cruhland.axiomatic.Logic.Biconditional where

open import Function using (id; _∘_)
open import Level using (_⊔_)

infixl 0 _↔_

record _↔_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  constructor ↔-intro
  field
    ↔-elimᴸ : A → B
    ↔-elimᴿ : B → A

open _↔_ using (↔-elimᴸ; ↔-elimᴿ) public

↔-refl : ∀ {α} {A : Set α} → A ↔ A
↔-refl = ↔-intro id id

↔-sym : ∀ {α β} {A : Set α} {B : Set β} → A ↔ B → B ↔ A
↔-sym (↔-intro ab ba) = ↔-intro ba ab

↔-trans :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → A ↔ B → B ↔ C → A ↔ C
↔-trans (↔-intro ab ba) (↔-intro bc cb) = ↔-intro (bc ∘ ab) (ba ∘ cb)

↔-bimap :
  ∀ {α β χ δ} {A : Set α} {B : Set β} {C : Set χ} {D : Set δ} →
    ((A → B) → (C → D)) → ((B → A) → (D → C)) → A ↔ B → C ↔ D
↔-bimap ab→cd ba→dc (↔-intro ab ba) = ↔-intro (ab→cd ab) (ba→dc ba)
