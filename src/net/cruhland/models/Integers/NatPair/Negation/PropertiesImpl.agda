open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.NatPair.Negation.BaseDefn PA using (NB)
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA as ℤ-

-- Export everything not defined here from the default implementation
import net.cruhland.axioms.Integers.Negation.PropertiesImplBase PA ZB Z+ NB
  as PropertiesImplBase
  hiding (neg-involutive)
open PropertiesImplBase public

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive a@{a⁺ — a⁻} =
  begin
    - (- a)
  ≃⟨⟩
    - (- (a⁺ — a⁻))
  ≃⟨⟩
    - (a⁻ — a⁺)
  ≃⟨⟩
    a⁺ — a⁻
  ≃⟨⟩
    a
  ∎
