open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.OrderingImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)

-- Export all definitions from the partial impl
open import net.cruhland.axioms.Integers.OrderingPartialImpl PA ZB Z+ Z- public
