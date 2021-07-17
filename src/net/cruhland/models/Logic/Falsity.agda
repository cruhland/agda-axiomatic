module net.cruhland.models.Logic.Falsity where

open import Relation.Binary.PropositionalEquality using (_≢_; sym)

-- Export standard library definitions
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic public
  using () renaming (⊥ to ⊥ᴸᴾ; ⊥-elim to ⊥ᴸᴾ-elim)
open import Relation.Nullary public using (¬_)

contra : ∀ {α β} {A : Set α} {B : Set β} → A → ¬ A → B
contra a ¬a = ⊥-elim (¬a a)

record ¬ⁱ_ {α} (A : Set α) : Set α where
  constructor ¬ⁱ-intro
  field
    elim : ¬ A

contrapositive : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → ¬ⁱ B → ¬ⁱ A
contrapositive f (¬ⁱ-intro ⊥-from-b) = ¬ⁱ-intro λ a → ⊥-from-b (f a)
