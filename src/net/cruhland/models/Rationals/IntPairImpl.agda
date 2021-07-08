open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPairImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

-- Export all sub-impls
open import net.cruhland.models.Rationals.IntPair.BaseImpl public
