open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl using (NegationBase)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.Negation.PropertiesDefnBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (NB : NegationBase PA ZB ZP Z+)
  where

open import net.cruhland.axioms.Integers.Negation.PropertiesDecl PA ZB ZP Z+
  using (NegationProperties)
import net.cruhland.axioms.Integers.Negation.PropertiesImplBase PA ZB ZP Z+ NB
  as NP

NP : NegationProperties NB
NP = record { NP }
