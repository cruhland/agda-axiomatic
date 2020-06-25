module net.cruhland.axiomatic.Logic.Falsity where

open import Level using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)

-- Export standard library definitions
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic public
  using () renaming (⊥ to ⊥̂; ⊥-elim to ⊥̂-elim)
open import Relation.Nullary public using (¬_)

¬sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
¬sym x≢y = λ y≡x → x≢y (sym y≡x)
