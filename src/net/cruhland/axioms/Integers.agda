open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Integers : Set₁ where
  field
    ZB : Base
    Z+ : Addition ZB

  open Addition Z+ public
  open Base ZB public
