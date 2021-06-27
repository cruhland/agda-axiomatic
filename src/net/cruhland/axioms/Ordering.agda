module net.cruhland.axioms.Ordering where

open import net.cruhland.axioms.Eq using (_≄_; Eq)
open import net.cruhland.models.Function using (flip)
open import net.cruhland.models.Logic using (¬_)

record LessThanOrEqual (A : Set) : Set₁ where
  constructor lessThanOrEqual
  infix 4 _≤_ _≥_ _≰_ _≱_
  field
    _≤_ : A → A → Set

  _≰_ : A → A → Set
  a ≰ b = ¬ (a ≤ b)

  _≥_ = flip _≤_
  _≱_ = flip _≰_

open LessThanOrEqual {{...}} public using (_≤_; _≥_; _≰_; _≱_)

record LessThan (A : Set) : Set₁ where
  constructor lessThan
  infix 4 _<_ _>_ _≮_ _≯_
  field
    _<_ : A → A → Set

  _≮_ : A → A → Set
  a ≮ b = ¬ (a < b)

  _>_ = flip _<_
  _≯_ = flip _≮_

open LessThan {{...}} public using (_<_; _>_; _≮_; _≯_)

record TotalOrder (A : Set) {{_ : Eq A}} : Set₁ where
  field
    {{≤-op}} : LessThanOrEqual A
    {{<-op}} : LessThan A
    <-from-≤≄ : {a b : A} → a ≤ b → a ≄ b → a < b

open TotalOrder {{...}} public using (<-from-≤≄)
