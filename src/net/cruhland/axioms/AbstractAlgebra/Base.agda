open import net.cruhland.models.Function using (flip; id)
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.AbstractAlgebra.Base where

data Hand : Set where
  handᴸ : Hand
  handᴿ : Hand

handRec : ∀ {α} {A : Set α} → A → A → Hand → A
handRec forᴸ forᴿ handᴸ = forᴸ
handRec forᴸ forᴿ handᴿ = forᴿ

forHand : ∀ {α β} {A : Set α} {B : Set β} → Hand → (A → A → B) → (A → A → B)
forHand = handRec id flip

forHandᶜ :
  ∀ {α β} {A : Set α} {B : Set β} {C : A → A → Set} (hand : Hand) →
  ((x y : A) {{_ : C x y}} → B) → ((x y : A) {{_ : forHand hand C x y}} → B)
forHandᶜ handᴸ = id
forHandᶜ handᴿ = flip

other : Hand → Hand
other = handRec handᴿ handᴸ

-- Short for "trivial constraint"
tc₁ :
  ∀ {α β} {A : Set α} {B : A → Set β} →
  ((x : A) → B x) → ((x : A) {{_ : ⊤}} → B x)
tc₁ f x = f x

tc₂ :
  ∀ {α β} {A : Set α} {B : A → A → Set β} →
  ((x y : A) → B x y) → ((x y : A) {{_ : ⊤}} → B x y)
tc₂ f x y = f x y
