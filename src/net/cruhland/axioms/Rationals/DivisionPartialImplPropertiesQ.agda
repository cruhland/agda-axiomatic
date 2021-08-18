import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplPropertiesQ
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)

private
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      (QR : Reciprocal QB QA QN QM)
      where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public
    open Reciprocal QR public

record DivisionPropertiesQ
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    : Set where
  private open module ℚ = RationalPredefs QB QA QN QM QR using (ℚ)

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    div-ℚ-defn : {p q : ℚ} {{_ : q ≄ 0}} → p / q ≃ p * q ⁻¹
    div-ℚ-subst-proof :
      {p q : ℚ} {{q≄0₁ q≄0₂ : q ≄ 0}} → (p / q) {{q≄0₁}} ≃ (p / q) {{q≄0₂}}
    q/q≃1 : {q : ℚ} {{_ : q ≄ 0}} → q / q ≃ 1
    *-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) * (r / s) ≃ (p * r) / (q * s)

  instance
    div-ℚ-distributive-+ᴿ : AA.Distributive AA.handᴿ _/_ _+_
    div-ℚ-distributive-+ᴿ = AA.distributive /-distrib-+ᴿ
      where
        /-distrib-+ᴿ :
          {p q r : ℚ} {{Cabc : p ≄ 0}} {{Cab : p ≄ 0}} {{Cac : p ≄ 0}} →
          ((q + r) / p) {{Cabc}} ≃ ((q / p) {{Cab}}) + ((r / p) {{Cac}})
        /-distrib-+ᴿ {p} {q} {r} {{Cabc}} {{Cab}} {{Cac}} =
          begin
            (q + r) / p
          ≃⟨ div-ℚ-defn ⟩
            (q + r) * p ⁻¹
          ≃⟨ AA.distrib {_⊙_ = AA.tc₂ _*_} ⟩
            q * p ⁻¹ + r * p ⁻¹
          ≃˘⟨ AA.subst₂ div-ℚ-defn ⟩
            ((q / p) {{Cabc}}) + r * p ⁻¹
          ≃˘⟨ AA.subst₂ div-ℚ-defn ⟩
            ((q / p) {{Cabc}}) + ((r / p) {{Cabc}})
          ≃⟨ AA.subst₂ div-ℚ-subst-proof ⟩
            ((q / p) {{Cab}}) + ((r / p) {{Cabc}})
          ≃⟨ AA.subst₂ div-ℚ-subst-proof ⟩
            ((q / p) {{Cab}}) + ((r / p) {{Cac}})
          ∎

    div-ℚ-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _/_ _≃_ _≃_
    div-ℚ-substitutiveᴸ = AA.substitutive₂ /-substᴸ
      where
        /-substᴸ :
          {q₁ q₂ r : ℚ} {{c₁ : r ≄ 0}} {{c₂ : r ≄ 0}} →
          q₁ ≃ q₂ → (q₁ / r) {{c₁}} ≃ (q₂ / r) {{c₂}}
        /-substᴸ {q₁} {q₂} {r} {{c₁}} {{c₂}} q₁≃q₂ =
          begin
            q₁ / r
          ≃⟨ div-ℚ-defn ⟩
            q₁ * (r ⁻¹)
          ≃⟨ AA.subst₂ q₁≃q₂ ⟩
            q₂ * (r ⁻¹) {{c₁}}
          ≃⟨ AA.substᴿ (AA.subst₁ Eq.refl) ⟩
            q₂ * (r ⁻¹) {{c₂}}
          ≃˘⟨ div-ℚ-defn ⟩
            q₂ / r
          ∎

    div-ℚ-substitutiveᴿ : AA.Substitutive₂ᶜ AA.handᴿ _/_ _≃_ _≃_
    div-ℚ-substitutiveᴿ = AA.substitutive₂ /-substᴿ
      where
        /-substᴿ :
          {q₁ q₂ p : ℚ} {{c₁ : q₁ ≄ 0}} {{c₂ : q₂ ≄ 0}} →
          q₁ ≃ q₂ → p / q₁ ≃ p / q₂
        /-substᴿ {q₁} {q₂} {p} q₁≃q₂ =
          begin
            p / q₁
          ≃⟨ div-ℚ-defn ⟩
            p * q₁ ⁻¹
          ≃⟨ AA.subst₂ (AA.subst₁ q₁≃q₂) ⟩
            p * q₂ ⁻¹
          ≃˘⟨ div-ℚ-defn ⟩
            p / q₂
          ∎

    div-ℚ-substitutive : AA.Substitutive²ᶜ _/_ _≃_ _≃_
    div-ℚ-substitutive = AA.substitutive²

    div-ℚ-comm-with-negᴸ : AA.FnOpCommutative AA.handᴸ -_ -_ _/_
    div-ℚ-comm-with-negᴸ = AA.fnOpCommutative /-negᴸ
      where
        /-negᴸ :
          {p q : ℚ} {{c₁ : q ≄ 0}} {{c₂ : q ≄ 0}} →
          - (p / q) {{c₁}} ≃ (- p / q) {{c₂}}
        /-negᴸ {p} {q} {{c₁}} {{c₂}} =
          begin
            - (p / q)
          ≃⟨ AA.subst₁ div-ℚ-defn ⟩
            - (p * q ⁻¹)
          ≃⟨ AA.fnOpCommᴸ ⟩
            - p * (q ⁻¹) {{c₁}}
          ≃⟨ AA.subst₂ (AA.subst₁ Eq.refl) ⟩
            - p * (q ⁻¹) {{c₂}}
          ≃˘⟨ div-ℚ-defn ⟩
            (- p) / q
          ∎

    div-ℚ-comm-with-negᴿ : AA.FnOpCommutative AA.handᴿ -_ -_ _/_
    div-ℚ-comm-with-negᴿ = AA.fnOpCommutative /-negᴿ
      where
        /-negᴿ :
          {p q : ℚ} {{c₁ : q ≄ 0}} {{c₂ : - q ≄ 0}} → - (p / q) ≃ p / (- q)
        /-negᴿ {p} {q} =
          begin
            - (p / q)
          ≃⟨ AA.subst₁ div-ℚ-defn ⟩
            - (p * q ⁻¹)
          ≃⟨ AA.fnOpCommᴿ ⟩
            p * - (q ⁻¹)
          ≃˘⟨ AA.subst₂ AA.compat₁ ⟩
            p * (- q) ⁻¹
          ≃˘⟨ div-ℚ-defn ⟩
            p / (- q)
          ∎

    div-ℚ-comm-with-neg : AA.FnOpCommutative² -_ -_ _/_
    div-ℚ-comm-with-neg = AA.fnOpCommutative²

    div-ℚ-absorptiveᴸ : AA.Absorptive AA.handᴸ _/_
    div-ℚ-absorptiveᴸ = AA.absorptive 0/q≃0
      where
        0/q≃0 : {q : ℚ} {{_ : q ≄ 0}} → 0 / q ≃ 0
        0/q≃0 {q} =
          begin
            0 / q
          ≃⟨ div-ℚ-defn ⟩
            0 * q ⁻¹
          ≃⟨ AA.absorb ⟩
            0
          ∎
