open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.Multiplication.BaseDecl PA as BaseDecl
import net.cruhland.axioms.Integers.Multiplication.PropertiesDecl PA
  as PropertiesDecl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Multiplication
    (ZB : Base)
    (Z+ : Addition ZB)
    (Z- : Negation ZB Z+)
    (ZS : Sign ZB Z+ Z-)
    : Set where
  open BaseDecl ZB Z+ Z- using (MultiplicationBase)
  open PropertiesDecl ZB Z+ Z- ZS using (MultiplicationProperties)

  field
    MB : MultiplicationBase
    MP : MultiplicationProperties MB

  open MultiplicationBase MB public
  open MultiplicationProperties MP public

-- Confirm that all impls conform to their decls
module _ where
  import net.cruhland.axioms.Integers.Multiplication.PropertiesDefnBase
