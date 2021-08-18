import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.MultiplicationPartialImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

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

record MultiplicationProperties
    (QB : Base) (QA : Addition QB) (QN : Negation QB QA) : Set where
  private open module ℚ = RationalPredefs QB QA QN using (ℚ)

  field
    {{star}} : Op.Star ℚ
    {{*-substitutive}} : AA.Substitutive² {A = ℚ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℚ} _*_
    {{*-associative}} : AA.Associative {A = ℚ} _*_
    {{*-identity}} : AA.Identity² {A = ℚ} _*_ 1
    {{*-distributive}} : AA.Distributive² {A = ℚ} (AA.tc₂ _*_) _+_
    *-neg-ident : {q : ℚ} → -1 * q ≃ - q

  instance
    *-comm-with-negᴸ : AA.FnOpCommutative AA.handᴸ -_ -_ (AA.tc₂ _*_)
    *-comm-with-negᴸ = AA.fnOpCommutative *-negᴸ
      where
        *-negᴸ : {p q : ℚ} → - (p * q) ≃ (- p) * q
        *-negᴸ {p} {q} =
          begin
            - (p * q)
          ≃˘⟨ *-neg-ident ⟩
            -1 * (p * q)
          ≃˘⟨ AA.assoc ⟩
            (-1 * p) * q
          ≃⟨ AA.subst₂ *-neg-ident ⟩
            (- p) * q
          ∎

    *-comm-with-negᴿ : AA.FnOpCommutative AA.handᴿ -_ -_ (AA.tc₂ _*_)
    *-comm-with-negᴿ = AA.fnOpCommutativeᴿ-from-fnOpCommutativeᴸ {A = ℚ}

    *-comm-with-neg : AA.FnOpCommutative² -_ -_ (AA.tc₂ _*_)
    *-comm-with-neg = AA.fnOpCommutative² {A = ℚ}

    *-absorptiveᴸ : AA.Absorptive AA.handᴸ (AA.tc₂ _*_)
    *-absorptiveᴸ = AA.absorptive *-absorbᴸ
      where
        *-absorbᴸ : {q : ℚ} → 0 * q ≃ 0
        *-absorbᴸ {q} =
          begin
            0 * q
          ≃˘⟨ AA.subst₂ AA.inv ⟩
            (1 + -1) * q
          ≃⟨ AA.distrib ⟩
            1 * q + -1 * q
          ≃⟨ AA.subst₂ AA.ident ⟩
            q + -1 * q
          ≃⟨ AA.subst₂ *-neg-ident ⟩
            q + (- q)
          ≃⟨ AA.inv ⟩
            0
          ∎

    *-absorptiveᴿ : AA.Absorptive AA.handᴿ (AA.tc₂ _*_)
    *-absorptiveᴿ = AA.absorptiveᴿ-from-absorptiveᴸ {A = ℚ}

    *-absorptive : AA.Absorptive² (AA.tc₂ _*_)
    *-absorptive = AA.absorptive² {A = ℚ}
