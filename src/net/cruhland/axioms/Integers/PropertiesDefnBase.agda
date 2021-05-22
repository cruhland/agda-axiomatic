open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.PropertiesDefnBase
  (PA : PeanoArithmetic) (ZB : Base PA) where

open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)
import net.cruhland.axioms.Integers.PropertiesImplBase PA ZB as ZP

ZP : Properties ZB
ZP = record { ZP }
