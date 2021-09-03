import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.NegationPartialImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl

private
  module IntegerPredefs (ZB : Base) (ZA : Addition ZB) where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public

record NegationProperties (ZB : Base) (ZA : Addition ZB) : Set₁ where
  private
    open module ℤ = IntegerPredefs ZB ZA using (ℤ)

  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
    {{neg-inverse}} : AA.Inverse² {A = ℤ} (AA.tc₁ -_) _+_ 0

  instance
    neg-injective : AA.Injective -_ _≃_ _≃_
    neg-injective = AA.injective neg-inject
      where
        neg-inject : {a₁ a₂ : ℤ} →  - a₁ ≃ - a₂ → a₁ ≃ a₂
        neg-inject {a₁} {a₂} -a₁≃-a₂ =
          begin
            a₁
          ≃˘⟨ AA.inv-involutive ⟩
            - (- a₁)
          ≃⟨ AA.subst₁ -a₁≃-a₂ ⟩
            - (- a₂)
          ≃⟨ AA.inv-involutive ⟩
            a₂
          ∎

    [-1]≄0 : -1 ≄ 0
    [-1]≄0 = AA.substᴿ AA.inv-ident (AA.subst₁ ℤ.1≄0)
