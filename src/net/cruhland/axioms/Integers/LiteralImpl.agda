import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_; _value_)
open import net.cruhland.axioms.Eq as Eq using (_≄_)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Operators as Op using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.axioms.Integers.LiteralImpl
  (PA : PeanoArithmetic) (ZB : Base PA) where

private
  open module ℕ = PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)

instance
  nat-literal : FromNatLiteral ℤ
  nat-literal = nat-literal-via ℕ

  1≄0 : (ℤ value 1) ≄ 0
  1≄0 = Eq.≄-intro λ 1:ℤ≃0:ℤ →
    let s0≃0 = AA.inject 1:ℤ≃0:ℤ
     in s0≃0 ↯ ℕ.step≄zero

  neg-literal : {{_ : Op.Dashᴸ ℤ}} → FromNegLiteral ℤ
  neg-literal = neg-literal-via-nat-literal
