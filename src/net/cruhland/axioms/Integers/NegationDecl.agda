import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.NegationDecl (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Negation (ZB : Base) : Set where
  private open module ℤ = Base ZB using (ℤ)

  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_

  instance
    neg-literal : FromNeg.Negative ℤ
    neg-literal = record { Constraint = const ⊤ ; fromNeg = λ n → - (n as ℤ) }
