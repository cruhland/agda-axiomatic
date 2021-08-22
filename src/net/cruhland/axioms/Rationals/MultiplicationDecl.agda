import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.MultiplicationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)

private
  module RationalPredefs
      (QB : Base) (QA : Addition QB) (QN : Negation QB QA) where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public
    open Negation QN public

record Multiplication
    (QB : Base) (QA : Addition QB) (QN : Negation QB QA) : Set where
  private open module ℚ = RationalPredefs QB QA QN using (ℚ)

  field
    {{star}} : Op.Star ℚ
    {{*-substitutive}} : AA.Substitutive² {A = ℚ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℚ} _*_
    {{*-associative}} : AA.Associative {A = ℚ} _*_
    {{*-identity}} : AA.Identity² {A = ℚ} _*_ 1
    {{*-absorptive}} : AA.Absorptive² {A = ℚ} (AA.tc₂ _*_)
    {{*-zero}} : AA.ZeroProduct {A = ℚ} _*_

    {{*-distributive-+}} : AA.Distributive² {A = ℚ} (AA.tc₂ _*_) _+_
    {{*-compatible-ℤ}} : AA.Compatible₂ {A = ℤ} (AA.tc₁ (_as ℚ)) _*_ _*_ _≃_

    *-neg-ident : {q : ℚ} → -1 * q ≃ - q
    {{*-comm-with-neg}} : AA.FnOpCommutative² {A = ℚ} -_ -_ (AA.tc₂ _*_)

    {{*-distributive-sub}} : AA.Distributive² {A = ℚ} (AA.tc₂ _*_) _-_
    {{neg-compatible-sub}} :
      AA.Compatible₂ {A = ℚ} (AA.tc₁ λ q → - q) _-_ _-_ _≃_
    neg-sub : {p q : ℚ} → - (p - q) ≃ q - p
