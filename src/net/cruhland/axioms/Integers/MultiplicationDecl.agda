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
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)

record Multiplication
    (ZB : Base)
    (ZP : Properties ZB)
    (Z+ : Addition ZB ZP)
    (Z- : Negation ZB ZP Z+)
    : Set where
  open BaseDecl ZB ZP Z+ Z- using (MultiplicationBase)
  open PropertiesDecl ZB ZP Z+ Z- using (MultiplicationProperties)

  field
    MB : MultiplicationBase
    MP : MultiplicationProperties MB

  open MultiplicationBase MB public
  open MultiplicationProperties MP public

-- Confirm that all impls conform to their decls
module _ where
  import net.cruhland.axioms.Integers.Multiplication.PropertiesDefnBase
