import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionDecl
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

record Division (QB : Base) (QA : Addition QB) (QN : Negation QB QA) : Set where
  private open module ℚ = RationalPredefs QB QA QN using (ℚ)

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    {{div-ℚ-substitutive}} : AA.Substitutive²ᶜ {A = ℚ} _/_ _≃_ _≃_
    {{div-ℚ-comm-with-neg}} : AA.FnOpCommutative² -_ -_ _/_

    {{div-ℤ}} : Op.Slash ℤ (_≄ 0) ℚ
    {{div-ℤ-substitutive}} : AA.Substitutive²ᶜ {A = ℤ} _/_ _≃_ _≃_
    {{div-ℤ-comm-with-neg}} : AA.FnOpCommutative² {B = ℤ} -_ -_ _/_

    a≃0-from-a/b≃0 : {a b : ℤ} {{_ : b ≄ 0}} → a / b ≃ 0 → a ≃ 0
