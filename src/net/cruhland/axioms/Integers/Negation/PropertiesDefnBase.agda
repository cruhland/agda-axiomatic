open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl using (NegationBase)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.Negation.PropertiesDefnBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (NB : NegationBase PA ZB Z+)
  where

open import net.cruhland.axioms.Integers.Negation.PropertiesDecl PA ZB Z+
  using (NegationProperties)
import net.cruhland.axioms.Integers.Negation.PropertiesImplBase PA ZB Z+ NB
  as NP

NP : NegationProperties NB
NP = record { NP }
