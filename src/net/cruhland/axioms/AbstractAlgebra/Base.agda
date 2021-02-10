module net.cruhland.axioms.AbstractAlgebra.Base where

open import net.cruhland.models.Function using (flip; id)

data Hand : Set where
  handᴸ : Hand
  handᴿ : Hand

handRec : ∀ {α} {A : Set α} → A → A → Hand → A
handRec forᴸ forᴿ handᴸ = forᴸ
handRec forᴸ forᴿ handᴿ = forᴿ

forHand : ∀ {α β} {A : Set α} {B : Set β} → Hand → (A → A → B) → (A → A → B)
forHand = handRec id flip

other : Hand → Hand
other = handRec handᴿ handᴸ
