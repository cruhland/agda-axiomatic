open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.AdditionDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as ZA

ZA : Addition ZB
ZA = record { ZA }
