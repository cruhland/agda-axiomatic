open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using (flip; id)
open import net.cruhland.models.Logic using (_∨_; ¬_)

module net.cruhland.axioms.Ordering where

record LessThanOrEqual (A : Set) : Set₁ where
  constructor lessThanOrEqual
  infix 4 _≤_ _≰_
  field
    _≤_ : A → A → Set

  _≰_ : A → A → Set
  x ≰ y = ¬ (x ≤ y)

open LessThanOrEqual {{...}} public using (_≤_; _≰_)
{-# DISPLAY LessThanOrEqual._≤_ _ x y = x ≤ y #-}

record GreaterThanOrEqual (A : Set) : Set₁ where
  constructor greaterThanOrEqual
  infix 4 _≥_ _≱_
  field
    _≥_ : A → A → Set

  _≱_ : A → A → Set
  x ≱ y = ¬ (x ≥ y)

open GreaterThanOrEqual {{...}} public using (_≥_; _≱_)
{-# DISPLAY GreaterThanOrEqual._≥_ _ x y = x ≥ y #-}

record NonStrictOrder (A : Set) : Set₁ where
  field
    {{lte}} : LessThanOrEqual A
    {{gte}} : GreaterThanOrEqual A

    ≤-flip : {x y : A} → x ≤ y → y ≥ x
    ≥-flip : {x y : A} → x ≥ y → y ≤ x

open NonStrictOrder {{...}} public using (≤-flip; ≥-flip)

record LessThan (A : Set) : Set₁ where
  constructor lessThan
  infix 4 _<_ _≮_
  field
    _<_ : A → A → Set

  _≮_ : A → A → Set
  x ≮ y = ¬ (x < y)

open LessThan {{...}} public using (_<_; _≮_)
{-# DISPLAY LessThan._<_ _ x y = x < y #-}

record GreaterThan (A : Set) : Set₁ where
  constructor greaterThan
  infix 4 _>_ _≯_
  field
    _>_ : A → A → Set

  _≯_ : A → A → Set
  x ≯ y = ¬ (x > y)

open GreaterThan {{...}} public using (_>_; _≯_)
{-# DISPLAY GreaterThan._>_ _ x y = x > y #-}

record StrictOrder (A : Set) : Set₁ where
  field
    {{lt}} : LessThan A
    {{gt}} : GreaterThan A

    <-flip : {x y : A} → x < y → y > x
    >-flip : {x y : A} → x > y → y < x

open StrictOrder {{...}} public using (<-flip; >-flip)

record TotalOrder (A : Set) {{_ : Eq A}} : Set₁ where
  field
    {{nonstrict}} : NonStrictOrder A
    {{strict}} : StrictOrder A
    <-from-≤≄ : {x y : A} → x ≤ y → x ≄ y → x < y

open TotalOrder {{...}} public using (<-from-≤≄)

-- Default implementations
module _ {A : Set} where

  gte-from-lte : {{_ : LessThanOrEqual A}} → GreaterThanOrEqual A
  gte-from-lte = greaterThanOrEqual (flip _≤_)

  lte-from-gte : {{_ : GreaterThanOrEqual A}} → LessThanOrEqual A
  lte-from-gte = lessThanOrEqual (flip _≥_)

  gt-from-lt : {{_ : LessThan A}} → GreaterThan A
  gt-from-lt = greaterThan (flip _<_)

  lt-from-gt : {{_ : GreaterThan A}} → LessThan A
  lt-from-gt = lessThan (flip _>_)

  gte-from-eq-gt : {{_ : Eq A}} {{_ : GreaterThan A}} → GreaterThanOrEqual A
  gte-from-eq-gt = greaterThanOrEqual λ x y → x > y ∨ x ≃ y

  lte-from-eq-lt : {{_ : Eq A}} {{_ : LessThan A}} → LessThanOrEqual A
  lte-from-eq-lt = lessThanOrEqual λ x y → x < y ∨ x ≃ y

  nonStrict-from-lte : (A → A → Set) → NonStrictOrder A
  nonStrict-from-lte _≤₀_ =
    let instance
          lte = lessThanOrEqual _≤₀_
          gte = gte-from-lte
     in record { ≤-flip = id ; ≥-flip = id }

  strict-from-lt : (A → A → Set) → StrictOrder A
  strict-from-lt _<₀_ =
    let instance
          lt = lessThan _<₀_
          gt = gt-from-lt
     in record { <-flip = id ; >-flip = id }
