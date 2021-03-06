module net.cruhland.models.Logic.Conjunction where

open import net.cruhland.models.Function using (id)

-- Export standard library definitions
open import Data.Product public using (curry; uncurry) renaming
  ( _×_ to _∧_
  ; _,_ to ∧-intro
  ; proj₁ to ∧-elimᴸ
  ; proj₂ to ∧-elimᴿ
  ; swap to ∧-comm
  )

∧-map :
  ∀ {α β χ δ} {A : Set α} {B : Set β} {C : Set χ} {D : Set δ} →
  (A → C) → (B → D) → A ∧ B → C ∧ D
∧-map f g (∧-intro a b) = ∧-intro (f a) (g b)

∧-mapᴸ :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (A → C) → A ∧ B → C ∧ B
∧-mapᴸ f a∧b = ∧-map f id a∧b

∧-mapᴿ :
  ∀ {α β δ} {A : Set α} {B : Set β} {D : Set δ} → (B → D) → A ∧ B → A ∧ D
∧-mapᴿ g a∧b = ∧-map id g a∧b

∧-dup : ∀ {α} {A : Set α} → A → A ∧ A
∧-dup a = ∧-intro a a

instance
  conjunction : ∀ {α β} {A : Set α} {B : Set β} {{_ : A}} {{_ : B}} → A ∧ B
  conjunction {{a}} {{b}} = ∧-intro a b
