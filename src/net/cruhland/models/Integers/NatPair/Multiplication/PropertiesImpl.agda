open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Multiplication.PropertiesImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.Multiplication.BaseDefn PA
  using (MB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)

-- Export everything from the default implementation
open import net.cruhland.axioms.Integers.Multiplication.PropertiesImplBase
  PA ZB ZP Z+ Z- MB public
