open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.OrderingDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.OrderingDecl PA using (Ordering)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)
import net.cruhland.models.Integers.NatPair.OrderingImpl PA as Z<

Z< : Ordering ZB Z+ Z- ZS
Z< = record { Z< }
