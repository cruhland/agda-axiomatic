module net.cruhland.axioms.Operators where

record Plus (A : Set) : Set where
  infixl 6 _+_
  field
    _+_ : A → A → A

open Plus {{...}} public

record Star (A : Set) : Set where
  infixl 7 _*_
  field
    _*_ : A → A → A

open Star {{...}} public

record Dashᴸ (A : Set) : Set where
  infix 8 -_
  field
    -_ : A → A

open Dashᴸ {{...}} public

record Dash₂ (A : Set) : Set where
  infixl 6 _-_
  field
    _-_ : A → A → A

open Dash₂ {{...}} public

subtraction : {A : Set} {{_ : Plus A}} {{_ : Dashᴸ A}} → Dash₂ A
subtraction = record { _-_ = λ x y → x + - y }
