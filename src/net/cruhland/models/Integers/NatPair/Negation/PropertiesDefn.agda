open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Negation.PropertiesDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.Negation.BaseDefn PA using (NB)
import net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl PA as NP

open import net.cruhland.axioms.Integers.Negation.PropertiesDecl PA ZB Z+
  using (NegationProperties)

NP : NegationProperties NB
NP = record { NP }
