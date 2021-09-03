import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_value_)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.LiteralImpl
  (PA : PeanoArithmetic) (Z : Integers PA) (QB : Base PA Z) where

private
  open module ℤ = Integers Z using (ℤ)
  open module ℚ = Base QB using (ℚ)

instance
  nat-literal : FromNatLiteral ℚ
  nat-literal = nat-literal-via ℤ

  1≄0 : 1 ≄ (ℚ value 0)
  1≄0 = AA.subst₁ ℤ.1≄0

  neg-literal : {{_ : Op.Dashᴸ ℚ}} → FromNegLiteral ℚ
  neg-literal = neg-literal-via-nat-literal
