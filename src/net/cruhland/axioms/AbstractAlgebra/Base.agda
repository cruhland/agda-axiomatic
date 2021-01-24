module net.cruhland.axioms.AbstractAlgebra.Base where

open import net.cruhland.models.Function using (flip; id)

data Hand : Set where
  handᴸ : Hand
  handᴿ : Hand

handRec : {A : Set} → A → A → Hand → A
handRec forᴸ forᴿ handᴸ = forᴸ
handRec forᴸ forᴿ handᴿ = forᴿ

forHand : {A : Set} → Hand → (A → A → A) → (A → A → A)
forHand = handRec id flip

other : Hand → Hand
other = handRec handᴿ handᴸ
