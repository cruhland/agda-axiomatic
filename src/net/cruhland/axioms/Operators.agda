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

record Dash₂ (A : Set) : Set where
  constructor dash₂
  infixl 6 _-_
  field
    _-_ : A → A → A

open Dash₂ {{...}} public

subtraction : {A : Set} {{_ : Plus A}} {{_ : Dashᴸ A}} → Dash₂ A
subtraction = dash₂ λ x y → x + - y

record Caret (A : Set) : Set where
  constructor caret
  infixr 8 _^_
  field
    _^_ : A → A → A

open Caret {{...}} public
