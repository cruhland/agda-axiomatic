open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Sign.PropertiesImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.Sign.BaseDefn PA using (SB)

-- Export everything from the default implementation
import net.cruhland.axioms.Integers.Sign.PropertiesImplBase PA ZB Z+ Z- SB
  as PropertiesImplBase
open PropertiesImplBase public
