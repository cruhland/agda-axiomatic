open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Multiplication.BaseDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.Multiplication.BaseDecl PA
  using (MultiplicationBase)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
import net.cruhland.models.Integers.NatPair.Multiplication.BaseImpl PA as MB
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)

MB : MultiplicationBase ZB Z+ Z-
MB = record { MB }
