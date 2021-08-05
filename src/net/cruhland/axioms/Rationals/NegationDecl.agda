import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.NegationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private module RationalPredefs (QB : Base) (QA : Addition QB) where
  open Addition QA public
  open Base QB public
  open LiteralImpl QB public

record Negation (QB : Base) (QA : Addition QB) : Set₁ where
  private open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{neg-dash}} : Op.Dashᴸ ℚ
    {{neg-substitutive}} : AA.Substitutive₁ {A = ℚ} -_ _≃_ _≃_
    {{neg-compatible-ℤ}} : AA.Compatible₁ {A = ℤ} (_as ℚ) -_ -_ _≃_
    {{+-inverse}} : AA.Inverse² {A = ℚ} (AA.tc₁ -_) _+_ 0

    {{sub-dash}} : Op.Dash₂ ℚ
