import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.MultiplicationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private module RationalPredefs (QB : Base) (QA : Addition QB) where
  open Addition QA public
  open Base QB public
  open LiteralImpl QB public

record Multiplication (QB : Base) (QA : Addition QB) : Set where
  private open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{star}} : Op.Star ℚ
    {{*-substitutive}} : AA.Substitutive² {A = ℚ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℚ} _*_
    {{*-associative}} : AA.Associative {A = ℚ} _*_
    {{*-identity}} : AA.Identity² {A = ℚ} _*_ 1

    {{*-distributive}} : AA.Distributive² {A = ℚ} _*_ _+_
    {{*-compatible-ℤ}} : AA.Compatible₂ {A = ℤ} (_as ℚ) _*_ _*_ _≃_
