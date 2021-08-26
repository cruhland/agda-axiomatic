import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.NegationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private
  open module ℤ = Integers Z using (ℤ)
  module RationalPredefs (QB : Base) (QA : Addition QB) where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public

record Negation (QB : Base) (QA : Addition QB) : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{neg-dash}} : Op.Dashᴸ ℚ
    {{neg-substitutive}} : AA.Substitutive₁ {A = ℚ} -_ _≃_ _≃_
    {{neg-compatible-ℤ}} : AA.Compatible₁ {A = ℤ} (AA.tc₁ (_as ℚ)) -_ -_ _≃_
    {{+-inverse}} : AA.Inverse² {A = ℚ} (AA.tc₁ λ q → - q) _+_ 0

    {{sub-dash}} : Op.Dash₂ ℚ
    {{sub-substitutive}} : AA.Substitutive² {A = ℚ} _-_ _≃_ _≃_
    sub-defn : {p q : ℚ} → p - q ≃ p + (- q)
    sub-negᴿ : {p q : ℚ} → p - (- q) ≃ p + q
    sub-same : {q : ℚ} → q - q ≃ 0
    p-q≃0-from-p≃q : {p q : ℚ} → p ≃ q → p - q ≃ 0
    p≃q-from-p-q≃0 : {p q : ℚ} → p - q ≃ 0 → p ≃ q
