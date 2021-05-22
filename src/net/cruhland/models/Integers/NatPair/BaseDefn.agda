open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.BaseDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.models.Integers.NatPair.BaseImpl PA as ZB

ZB : Base
ZB = record { ZB }
