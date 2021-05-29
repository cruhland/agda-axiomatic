open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.MultiplicationImpl
  (PA : PeanoArithmetic) where

import net.cruhland.models.Integers.NatPair.Multiplication.BaseImpl PA
  as BaseImpl
import net.cruhland.models.Integers.NatPair.Multiplication.PropertiesImpl PA
  as PropertiesImpl

-- Re-export contents of child modules
open BaseImpl public
open PropertiesImpl public
