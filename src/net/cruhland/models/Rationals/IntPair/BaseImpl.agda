open import net.cruhland.axioms.Cast as Cast using (_As_)
open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.BaseImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open Integers Z using (ℤ)

record ℚ : Set where
  constructor _//_
  field
    numerator denominator : ℤ
    {{denominator≄ⁱ0}} : denominator ≄ⁱ 0

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = Cast.As-intro (_// 1)

  from-ℕ : ℕ As ℚ
  from-ℕ = Cast.via ℤ

  from-Nat : Nat As ℚ
  from-Nat = Cast.via ℕ

  from-literal : FromNatLiteral ℚ
  from-literal = nat-literal-from-cast
