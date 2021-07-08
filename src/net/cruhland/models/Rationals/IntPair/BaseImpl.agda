open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.BaseImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open Integers Z using (ℤ)

record ℚ : Set where
  constructor _//_
  field
    n d : ℤ
    {{d≄ⁱ0}} : d ≄ⁱ 0
