import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.NegationPartialImplDerived
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private
  module RationalPredefs (QB : Base) (QA : Addition QB) where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public

record NegationDerived (QB : Base) (QA : Addition QB) : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{neg-dash}} : Op.Dashᴸ ℚ
    {{+-inverse}} : AA.Inverse² {A = ℚ} (AA.tc₁ λ q → - q) _+_ 0

    {{sub-dash}} : Op.Dash₂ ℚ
    {{sub-substitutive}} : AA.Substitutive² {A = ℚ} _-_ _≃_ _≃_
    sub-same : {q : ℚ} → q - q ≃ 0

  p-q≃0-from-p≃q : {p q : ℚ} → p ≃ q → p - q ≃ 0
  p-q≃0-from-p≃q {p} {q} p≃q =
    begin
      p - q
    ≃⟨ AA.subst₂ p≃q ⟩
      q - q
    ≃⟨ sub-same ⟩
      0
    ∎
