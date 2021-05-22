open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.NegationDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)
import net.cruhland.axioms.Integers.Negation.BaseDecl PA as BaseDecl
import net.cruhland.axioms.Integers.Negation.PropertiesDecl PA as PropertiesDecl

record Negation
    (ZB : Base) (ZP : Properties ZB) (Z+ : Addition ZB ZP) : Set₁ where
  open BaseDecl ZB ZP Z+ using (NegationBase)
  open PropertiesDecl ZB ZP Z+ using (NegationProperties)

  field
    NB : NegationBase
    NP : NegationProperties NB

  open NegationBase NB public
  open NegationProperties NP public

-- Confirm that all impls conform to their decls
module _ where
  import net.cruhland.axioms.Integers.Negation.PropertiesDefnBase
