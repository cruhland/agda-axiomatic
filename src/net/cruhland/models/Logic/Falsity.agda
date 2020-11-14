module net.cruhland.models.Logic.Falsity where

open import Relation.Binary.PropositionalEquality using (_≢_; sym)

-- Export standard library definitions
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic public
  using () renaming (⊥ to ⊥ᴸᴾ; ⊥-elim to ⊥ᴸᴾ-elim)
open import Relation.Nullary public using (¬_)

record ¬ⁱ_ {α} (A : Set α) : Set α where
  constructor ¬ⁱ-intro
  field
    elim : ¬ A
