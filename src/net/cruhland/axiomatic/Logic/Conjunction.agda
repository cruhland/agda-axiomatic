module net.cruhland.axiomatic.Logic.Conjunction where

open import Function using (id)

-- Export standard library definitions
open import Data.Product public using () renaming
  (_×_ to _∧_
  ; _,_ to ∧-intro
  ; proj₁ to ∧-elimᴸ
  ; proj₂ to ∧-elimᴿ
  ; swap to ∧-comm
  )

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

∧-dup : ∀ {α} {A : Set α} → A → A ∧ A
∧-dup a = ∧-intro a a
