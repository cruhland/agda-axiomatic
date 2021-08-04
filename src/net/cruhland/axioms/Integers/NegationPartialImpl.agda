import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.NegationPartialImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl

module _ (ZB : Base) (ZA : Addition ZB) where

  private module ℤ where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public

  open ℤ using (ℤ)

  record NegationProperties : Set₁ where
    field
      {{neg-dash}} : Op.Dashᴸ ℤ
      {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
      {{neg-inverse}} : AA.Inverse² {A = ℤ} (AA.tc₁ -_) _+_ 0

    neg-involutive : {a : ℤ} → - (- a) ≃ a
    neg-involutive {a} =
      begin
        - (- a)
      ≃˘⟨ AA.ident ⟩
        - (- a) + 0
      ≃˘⟨ AA.subst₂ AA.inv ⟩
        - (- a) + ((- a) + a)
      ≃˘⟨ AA.assoc ⟩
        (- (- a) + (- a)) + a
      ≃⟨ AA.subst₂ AA.inv ⟩
        0 + a
      ≃⟨ AA.ident ⟩
        a
      ∎

    instance
      neg-injective : AA.Injective -_ _≃_ _≃_
      neg-injective = AA.injective neg-inject
        where
          neg-inject : {a₁ a₂ : ℤ} →  - a₁ ≃ - a₂ → a₁ ≃ a₂
          neg-inject {a₁} {a₂} -a₁≃-a₂ =
            begin
              a₁
            ≃˘⟨ neg-involutive ⟩
              - (- a₁)
            ≃⟨ AA.subst₁ -a₁≃-a₂ ⟩
              - (- a₂)
            ≃⟨ neg-involutive ⟩
              a₂
            ∎

    neg-zero : - 0 ≃ 0
    neg-zero =
      begin
        - 0
      ≃˘⟨ AA.ident ⟩
        - 0 + 0
      ≃⟨ AA.inv ⟩
        0
      ∎
