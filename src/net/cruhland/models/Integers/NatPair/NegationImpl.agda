open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl as BaseImpl
import net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl
  as PropertiesImpl

module net.cruhland.models.Integers.NatPair.NegationImpl
  (PA : PeanoArithmetic) where

-- Re-export contents of child modules
open BaseImpl PA public
open PropertiesImpl PA public
