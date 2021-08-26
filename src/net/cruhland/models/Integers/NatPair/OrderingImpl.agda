open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.OrderingImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (ZM)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

-- Export all definitions from the default impl
open import net.cruhland.axioms.Integers.OrderingDefaultImpl PA ZB ZA ZN ZM ZS
  public
