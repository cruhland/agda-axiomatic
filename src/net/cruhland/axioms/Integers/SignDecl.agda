open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
import net.cruhland.axioms.Integers.Sign.BaseDecl PA as BaseDecl
import net.cruhland.axioms.Integers.Sign.PropertiesDecl PA as PropertiesDecl

record Sign (ZB : Base) (Z+ : Addition ZB) (Z- : Negation ZB Z+) : Set₁ where
  open BaseDecl ZB Z+ Z- using (SignBase)
  open PropertiesDecl ZB Z+ Z- using (SignProperties)

  field
    SB : SignBase
    SP : SignProperties SB

  open SignBase SB public
  open SignProperties SP public

-- Confirm that all impls conform to their decls
module _ (ZB : Base) (Z+ : Addition ZB) (Z- : Negation ZB Z+) where
  open PropertiesDecl ZB Z+ Z- using (SignProperties)
  import net.cruhland.axioms.Integers.Sign.PropertiesImplBase PA ZB Z+ Z-
    as PropertiesImplBase

  propertiesImplBase : ∀ SB → SignProperties SB
  propertiesImplBase SB = record { PropertiesImplBase SB }
