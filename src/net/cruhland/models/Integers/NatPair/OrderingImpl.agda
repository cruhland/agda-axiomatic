open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.OrderingImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (Z*)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

-- Export all definitions from the default impl
open import net.cruhland.axioms.Integers.OrderingDefaultImpl PA ZB Z+ Z- ZS Z*
  public
