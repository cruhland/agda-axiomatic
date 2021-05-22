open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.NegationImpl
  (PA : PeanoArithmetic) where

import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl PA
  as PropertiesImpl

-- Re-export contents of child modules
open BaseImpl public
open PropertiesImpl public
