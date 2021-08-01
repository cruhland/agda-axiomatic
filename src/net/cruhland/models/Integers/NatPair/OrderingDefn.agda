open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.OrderingDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.OrderingDecl PA using (Ordering)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)
import net.cruhland.models.Integers.NatPair.OrderingImpl PA as ZO

ZO : Ordering ZB ZA ZN ZS
ZO = record { ZO }
