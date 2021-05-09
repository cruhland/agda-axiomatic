open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

record Integers : Set₁ where
  field
    ZB : Base
    Z+ : Addition ZB
    Z- : Negation ZB Z+

  open Addition Z+ public
  open Base ZB public
  open Negation Z- public
