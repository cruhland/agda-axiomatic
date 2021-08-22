import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplDerivedQ
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)

private
  open module ℤ = Integers Z using (ℤ)
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
    open Negation QN public
    open Multiplication QM public

record DivisionDerivedQ
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    : Set where
  private
    open module ℚ = RationalPredefs QB QA QN QM QR using (ℚ)

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    {{div-ℚ-substitutive}} : AA.Substitutive²ᶜ {A = ℚ} _/_ _≃_ _≃_
    {{div-ℚ-distributive-+ᴿ}} : AA.Distributive AA.handᴿ _/_ _+_
    div-ℚ-subst-proof :
      {p q : ℚ} {{q≄0₁ q≄0₂ : q ≄ 0}} → (p / q) {{q≄0₁}} ≃ (p / q) {{q≄0₂}}
    q/q≃1 : {q : ℚ} {{_ : q ≄ 0}} → q / q ≃ 1
    *-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) * (r / s) ≃ (p * r) / (q * s)

  instance
    div-ℚ-cancellative-*ᴸ :
      AA.Cancellativeᶜ AA.handᴸ {A = ℚ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0)
    div-ℚ-cancellative-*ᴸ = AA.cancellative /-cancel-*ᴸ
      where
        /-cancel-*ᴸ :
          {p : ℚ} {{c : p ≄ 0}} {q r : ℚ} {{c~ : r ≄ 0}} {{c≈ : p * r ≄ 0}} →
          (p * q) / (p * r) ≃ q / r
        /-cancel-*ᴸ {p} {{p≄0}} {q} {r} {{r≄0}} {{pr≄0}} =
          let instance
                pr≄0-from-nonzero = AA.nonzero-prod {{a≄0 = p≄0}} {{r≄0}}
           in begin
                ((p * q) / (p * r)) {{pr≄0}}
              ≃⟨ div-ℚ-subst-proof ⟩
                ((p * q) / (p * r)) {{pr≄0-from-nonzero}}
              ≃˘⟨ *-div-ℚ ⟩
                (p / p) * (q / r)
              ≃⟨ AA.subst₂ q/q≃1 ⟩
                1 * (q / r)
              ≃⟨ AA.ident ⟩
                q / r
              ∎

    div-ℚ-cancellative-*ᴿ :
      AA.Cancellativeᶜ AA.handᴿ {A = ℚ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0)
    div-ℚ-cancellative-*ᴿ = AA.cancelᴿ-from-cancelᴸ-comm₂
      where
        instance ≃0-subst = AA.NeqProperties.≄-substitutive₁ᴸ

    div-ℚ-cancellative-* :
      AA.Cancellative²ᶜ {A = ℚ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0) (_≄ 0)
    div-ℚ-cancellative-* = AA.cancellative²

  +-div-ℚ :
    {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
    let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
     in (p / q) + (r / s) ≃ (p * s + q * r) / (q * s)
  +-div-ℚ {p} {q} {r} {s} {{q≄0}} {{s≄0}} =
    let instance
          qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
     in begin
          (p / q) + (r / s)
        ≃˘⟨ AA.subst₂ AA.cancel ⟩
          ((p * s) / (q * s)) + (r / s)
        ≃˘⟨ AA.subst₂ AA.cancel ⟩
          ((p * s) / (q * s)) + ((q * r) / (q * s))
        ≃˘⟨ AA.distrib {_⊙_ = _/_} ⟩
          (p * s + q * r) / (q * s)
        ∎
