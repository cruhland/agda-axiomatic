open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Integers.Sign.BaseDecl using (SignBase)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.Sign.PropertiesDefnBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (Z- : Negation PA ZB ZP Z+)
  (SB : SignBase PA ZB ZP Z+ Z-)
  where

open import net.cruhland.axioms.Integers.Sign.PropertiesDecl PA ZB ZP Z+ Z-
  using (SignProperties)
import net.cruhland.axioms.Integers.Sign.PropertiesImplBase PA ZB ZP Z+ Z- SB
  as SP

SP : SignProperties SB
SP = record { SP }
