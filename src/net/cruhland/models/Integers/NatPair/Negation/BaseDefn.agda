open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Negation.BaseDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.Negation.BaseDecl PA
  using (NegationBase)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA as NB

NB : NegationBase ZB Z+
NB = record { NB }
