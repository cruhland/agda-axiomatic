open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Integers : Set₁ where
  field
    ZB : Base
    ZP : Properties ZB
    Z+ : Addition ZB ZP
    Z- : Negation ZB ZP Z+
    ZS : Sign ZB ZP Z+ Z-
    Z* : Multiplication ZB ZP Z+ Z-

  open Addition Z+ public
  open Base ZB public
  open Multiplication Z* public
  open Negation Z- public
  open Properties ZP public
  open Sign ZS public

-- Confirm that all impls conform to their decls
module _ where
  import net.cruhland.axioms.Integers.PropertiesDefnBase
