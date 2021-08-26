module net.cruhland.models.Logic.Falsity where

-- Export standard library definitions
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic public
  using () renaming (⊥ to ⊥ᴸᴾ; ⊥-elim to ⊥ᴸᴾ-elim)

-- Define as a record so typeclass instances can be of type ¬ A
infix 3 ¬_
record ¬_ {α} (A : Set α) : Set α where
  constructor ¬-intro
  field
    elim : A → ⊥

-- Helper for working with contradictions
-- Performs ¬-elim and ⊥-elim in one step
infix 2 _↯_
_↯_ : ∀ {α β} {A : Set α} {B : Set β} → A → ¬ A → B
a ↯ (¬-intro ⊥-from-a) = ⊥-elim (⊥-from-a a)

contrapositive : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → ¬ B → ¬ A
contrapositive f ¬b = ¬-intro λ a → let b = f a in b ↯ ¬b
