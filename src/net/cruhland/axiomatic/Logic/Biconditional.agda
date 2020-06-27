module net.cruhland.axiomatic.Logic.Biconditional where

open import Function using (id; _∘_)
open import Level using (_⊔_)
open import net.cruhland.axiomatic.Logic.Conjunction
  using (_∧_; ∧-intro; ∧-comm; ∧-elimᴸ; ∧-elimᴿ; ∧-map)

infixl 0 _↔_

_↔_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A ↔ B = (A → B) ∧ (B → A)

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
