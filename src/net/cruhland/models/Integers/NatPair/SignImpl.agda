open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.SignImpl
  (PA : PeanoArithmetic) where

import net.cruhland.models.Integers.NatPair.Sign.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.Sign.PropertiesImpl PA
  as PropertiesImpl

-- Re-export contents of child modules
open BaseImpl public
open PropertiesImpl public
