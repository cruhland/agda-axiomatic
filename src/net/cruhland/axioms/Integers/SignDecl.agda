open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)
import net.cruhland.axioms.Integers.Sign.BaseDecl PA as BaseDecl
import net.cruhland.axioms.Integers.Sign.PropertiesDecl PA as PropertiesDecl

record Sign
    (ZB : Base)
    (ZP : Properties ZB)
    (Z+ : Addition ZB ZP)
    (Z- : Negation ZB ZP Z+)
    : Set₁ where
  open BaseDecl ZB ZP Z+ Z- using (SignBase)
  open PropertiesDecl ZB ZP Z+ Z- using (SignProperties)

  field
    SB : SignBase
    SP : SignProperties SB

  open SignBase SB public
  open SignProperties SP public

-- Confirm that all impls conform to their decls
module _ where
  import net.cruhland.axioms.Integers.Sign.PropertiesDefnBase