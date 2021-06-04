open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.NegationDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
import net.cruhland.models.Integers.NatPair.NegationImpl PA as Z-

Z- : Negation ZB Z+
Z- = record { Z- }
