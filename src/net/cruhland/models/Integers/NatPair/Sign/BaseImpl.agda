open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Sign.BaseImpl
  (PA : PeanoArithmetic) where

-- Choose an impl to be the default
open import net.cruhland.models.Integers.NatPair.Sign.BaseImplLt PA public
