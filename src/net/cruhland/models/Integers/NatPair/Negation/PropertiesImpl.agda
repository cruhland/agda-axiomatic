open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤ
  using (ℤ; ≃₀-intro)
open import net.cruhland.models.Integers.NatPair.Negation.BaseDefn PA using (NB)
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA as ℤ-
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)

-- Export everything not defined here from the default implementation
import net.cruhland.axioms.Integers.Negation.PropertiesImplBase PA ZB ZP Z+ NB
  as PropertiesImplBase
  hiding (neg-involutive)
open PropertiesImplBase public

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃₀-intro Eq.refl
