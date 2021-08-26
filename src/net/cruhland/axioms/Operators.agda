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
