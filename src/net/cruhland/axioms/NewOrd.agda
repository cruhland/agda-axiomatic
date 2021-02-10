module net.cruhland.axioms.NewOrd where

open import net.cruhland.models.Function using (flip)
open import net.cruhland.models.Logic using (¬_)

record BaseOrd (A : Set) : Set₁ where
  infix 4 _≤_ _≥_ _<_ _>_ _≰_ _≱_ _≮_ _≯_
  field
    _≤_ : A → A → Set
    _<_ : A → A → Set

  _≰_ : A → A → Set
  a ≰ b = ¬ (a ≤ b)

  _≮_ : A → A → Set
  a ≮ b = ¬ (a < b)

  _≥_ = flip _≤_
  _>_ = flip _<_
  _≱_ = flip _≰_
  _≯_ = flip _≮_

open BaseOrd {{...}} public using (_≤_; _<_; _>_; _≮_)
