open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.PropertiesDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
import net.cruhland.models.Integers.NatPair.PropertiesImpl PA as ZP

ZP : Properties ZB
ZP = record { ZP }
