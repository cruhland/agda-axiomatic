open import net.cruhland.axioms.Cast using (_As_)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.BaseDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open Integers Z using (ℤ)

record Base : Set₁ where
  field
    ℚ : Set
    {{decEq}} : DecEq ℚ
    {{from-ℤ}} : ℤ As ℚ
    {{nat-literal}} : FromNatLiteral ℚ
