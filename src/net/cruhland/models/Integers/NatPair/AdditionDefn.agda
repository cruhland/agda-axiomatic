open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.AdditionDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as Z+

Z+ : Addition ZB ZP
Z+ = record { Z+ }
