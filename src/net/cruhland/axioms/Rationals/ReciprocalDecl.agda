import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _*_; _⁻¹)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.ReciprocalDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)

private
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public

record Reciprocal
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    : Set₁ where
  private open module ℚ = RationalPredefs QB QA QN QM using (ℚ)

  field
    {{reciprocal}} : Op.SupNegOne ℚ (_≄ 0)
    {{recip-substitutive}} : AA.Substitutive₁ᶜ {A = ℚ} _⁻¹ _≃_ _≃_

    {{recip-compat-neg}} : AA.Compatible₁ _⁻¹ -_ -_ _≃_
    {{*-inverse}} : AA.Inverse² _⁻¹ _*_ 1
