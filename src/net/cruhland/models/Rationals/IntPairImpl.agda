open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPairImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

-- Export all sub-impls
open import net.cruhland.models.Rationals.IntPair.AdditionImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.NegationImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z public
