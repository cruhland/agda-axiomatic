open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl PA
  using (NegationBase)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as ℤ+
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (ℤ; ≃₀-intro)
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA as ℤ-

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃₀-intro Eq.refl

-- Export everything not defined here from the default implementation
private
  base : Base
  base = record { ℤB }

  addition : Addition base
  addition = record { ℤ+ }

  negationBase : NegationBase base addition
  negationBase = record { ℤ- }

import net.cruhland.axioms.Integers.Negation.PropertiesImplBase PA
  as PropertiesImplBase
open PropertiesImplBase base addition negationBase public
  hiding (neg-involutive)
