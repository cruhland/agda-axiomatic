module net.cruhland.axioms.AbstractAlgebra.Base where

open import net.cruhland.models.Function using (flip; id)

data Hand : Set where
  handᴸ : Hand
  handᴿ : Hand

forHand : {A : Set} → Hand → (A → A → A) → (A → A → A)
forHand handᴸ = id
forHand handᴿ = flip

other : Hand → Hand
other handᴸ = handᴿ
other handᴿ = handᴸ
