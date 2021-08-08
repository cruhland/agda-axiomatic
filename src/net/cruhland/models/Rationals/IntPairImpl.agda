open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPairImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

-- Export all sub-impls
open import net.cruhland.models.Rationals.IntPair.AdditionImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.DivisionImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.NegationImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z public
open import net.cruhland.models.Rationals.IntPair.SignImpl PA Z public

open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
