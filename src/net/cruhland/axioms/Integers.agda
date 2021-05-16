open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Integers : Set₁ where
  field
    ZB : Base
    Z+ : Addition ZB
    Z- : Negation ZB Z+
    ZS : Sign ZB Z+ Z-
    Z* : Multiplication ZB

  open Addition Z+ public
  open Base ZB public
  open Multiplication Z* public
  open Negation Z- public
  open Sign ZS public
