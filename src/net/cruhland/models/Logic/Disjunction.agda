open import Level using (0ℓ)
open import net.cruhland.models.Function using (_∘_; id)
open import net.cruhland.models.Logic.Falsity
  using (⊥ᴸᴾ; ⊥ᴸᴾ-elim; ¬_; ¬-intro; _↯_)

module net.cruhland.models.Logic.Disjunction where

-- Export standard library definitions
open import Data.Sum public using () renaming
  ( _⊎_ to _∨_
  ; inj₁ to ∨-introᴸ
  ; inj₂ to ∨-introᴿ
  ; [_,_]′ to ∨-rec
  ; fromInj₁ to ∨-recᴸ
  ; fromInj₂ to ∨-recᴿ
  ; swap to ∨-comm
  ; map to ∨-map
  ; map₁ to ∨-mapᴸ
  ; map₂ to ∨-mapᴿ
  )

∨-merge : ∀ {α} {A : Set α} → A ∨ A → A
∨-merge = ∨-rec id id

∨-assocᴸᴿ :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assocᴸᴿ (∨-introᴸ (∨-introᴸ a)) = ∨-introᴸ a
∨-assocᴸᴿ (∨-introᴸ (∨-introᴿ b)) = ∨-introᴿ (∨-introᴸ b)
∨-assocᴸᴿ (∨-introᴿ c) = ∨-introᴿ (∨-introᴿ c)

∨-assocᴿᴸ :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
∨-assocᴿᴸ (∨-introᴸ a) = ∨-introᴸ (∨-introᴸ a)
∨-assocᴿᴸ (∨-introᴿ (∨-introᴸ b)) = ∨-introᴸ (∨-introᴿ b)
∨-assocᴿᴸ (∨-introᴿ (∨-introᴿ c)) = ∨-introᴿ c

-- Interactions with falsity (⊥) and negation (¬)
∨-identᴸ : ∀ {α β} {B : Set β} → ⊥ᴸᴾ {α} ∨ B → B
∨-identᴸ = ∨-recᴿ ⊥ᴸᴾ-elim

∨-identᴿ : ∀ {α β} {A : Set α} → A ∨ ⊥ᴸᴾ {β} → A
∨-identᴿ = ∨-recᴸ ⊥ᴸᴾ-elim

∨-forceᴸ : ∀ {α β} {A : Set α} {B : Set β} → ¬ B → A ∨ B → A
∨-forceᴸ ¬b = ∨-identᴿ {β = 0ℓ} ∘ ∨-mapᴿ (_↯ ¬b)

∨-forceᴿ : ∀ {α β} {A : Set α} {B : Set β} → ¬ A → A ∨ B → B
∨-forceᴿ ¬a = ∨-identᴸ {α = 0ℓ} ∘ ∨-mapᴸ (_↯ ¬a)

¬[a∨b]-from-¬a∧¬b : ∀ {α β} {A : Set α} {B : Set β} → ¬ A → ¬ B → ¬ (A ∨ B)
¬[a∨b]-from-¬a∧¬b ¬a ¬b = ¬-intro λ a∨b → ∨-rec (_↯ ¬a) (_↯ ¬b) a∨b
