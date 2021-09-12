open import net.cruhland.models.Logic using (¬_)

module net.cruhland.axioms.Operators where

record Plus (A : Set) : Set where
  constructor plus
  infixl 6 _+_
  field
    _+_ : A → A → A

open Plus {{...}} public

{-# DISPLAY Plus._+_ _ a b = a + b #-}

record Star (A : Set) : Set where
  constructor star
  infixl 7 _*_
  field
    _*_ : A → A → A

open Star {{...}} public

{-# DISPLAY Star._*_ _ a b = a * b #-}

record Dashᴸ (A : Set) : Set where
  constructor dashᴸ
  infix 8 -_
  field
    -_ : A → A

open Dashᴸ {{...}} public

{-# DISPLAY Dashᴸ.-_ _ a = - a #-}

record Dash₂ (A : Set) : Set where
  constructor dash₂
  infixl 6 _-_
  field
    _-_ : A → A → A

open Dash₂ {{...}} public

{-# DISPLAY Dash₂._-_ _ a b = a - b #-}

subtraction : {A : Set} {{_ : Plus A}} {{_ : Dashᴸ A}} → Dash₂ A
subtraction = dash₂ λ x y → x + - y

record SupNegOne (A : Set) (C : A → Set) : Set where
  constructor supNegOne
  infix 8 _⁻¹
  field
    _⁻¹ : (a : A) {{_ : C a}} → A

open SupNegOne {{...}} public

{-# DISPLAY SupNegOne._⁻¹ _ a = a ⁻¹ #-}

record Slash (A : Set) (C : A → Set) (B : Set) : Set where
  constructor slash
  infixl 7 _/_
  field
    _/_ : (x y : A) {{_ : C y}} → B

open Slash {{...}} public

{-# DISPLAY Slash._/_ _ x y = x / y #-}

division :
  {A : Set} {C : A → Set} {{_ : Star A}} {{_ : SupNegOne A C}} → Slash A C A
division = slash λ x y → x * y ⁻¹

record Caret (A : Set) : Set where
  constructor caret
  infixr 8 _^_
  field
    _^_ : A → A → A

open Caret {{...}} public

{-# DISPLAY Caret._^_ _ a b = a ^ b #-}

record LtEq (A : Set) : Set₁ where
  constructor ltEq
  infix 4 _≤_ _≰_
  field
    _≤_ : A → A → Set

  _≰_ : A → A → Set
  x ≰ y = ¬ (x ≤ y)

open LtEq {{...}} public

{-# DISPLAY LtEq._≤_ _ x y = x ≤ y #-}
{-# DISPLAY LtEq._≰_ _ x y = x ≰ y #-}

record GtEq (A : Set) : Set₁ where
  constructor gtEq
  infix 4 _≥_ _≱_
  field
    _≥_ : A → A → Set

  _≱_ : A → A → Set
  x ≱ y = ¬ (x ≥ y)

open GtEq {{...}} public

{-# DISPLAY GtEq._≥_ _ x y = x ≥ y #-}
{-# DISPLAY GtEq._≱_ _ x y = x ≱ y #-}

record Lt (A : Set) : Set₁ where
  constructor lt
  infix 4 _<_ _≮_
  field
    _<_ : A → A → Set

  _≮_ : A → A → Set
  x ≮ y = ¬ (x < y)

open Lt {{...}} public

{-# DISPLAY Lt._<_ _ x y = x < y #-}
{-# DISPLAY Lt._≮_ _ x y = x ≮ y #-}

record Gt (A : Set) : Set₁ where
  constructor gt
  infix 4 _>_ _≯_
  field
    _>_ : A → A → Set

  _≯_ : A → A → Set
  x ≯ y = ¬ (x > y)

open Gt {{...}} public

{-# DISPLAY Gt._>_ _ x y = x > y #-}
{-# DISPLAY Gt._≯_ _ x y = x ≯ y #-}
