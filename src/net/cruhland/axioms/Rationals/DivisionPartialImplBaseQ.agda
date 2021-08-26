import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.AdditionDecl using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.axioms.Rationals.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl using (Reciprocal)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplBaseQ
  (PA : PeanoArithmetic)
  (Z : Integers PA)
  (QB : Base PA Z)
  (QA : Addition PA Z QB)
  (QN : Negation PA Z QB QA)
  (QM : Multiplication PA Z QB QA QN)
  (QR : Reciprocal PA Z QB QA QN QM)
  where

import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private
  module ℚ where
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public

open ℚ using (ℚ)

instance
  div-ℚ : Op.Slash ℚ (_≄ 0) ℚ
  div-ℚ = Op.division

div-ℚ-defn : {p q : ℚ} {{_ : q ≄ 0}} → p / q ≃ p * q ⁻¹
div-ℚ-defn = Eq.refl

*-div-ℚ :
  {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
  let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
   in (p / q) * (r / s) ≃ (p * r) / (q * s)
*-div-ℚ {p} {q} {r} {s} {{q≄0}} {{s≄0}} =
  let instance
        qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
   in begin
        (p / q) * (r / s)
      ≃⟨⟩
        (p * q ⁻¹) * (r * s ⁻¹)
      ≃⟨ AA.transpose ⟩
        (p * r) * (q ⁻¹ * s ⁻¹)
      ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
        (p * r) * (q * s) ⁻¹
      ≃⟨⟩
        (p * r) / (q * s)
      ∎

q/q≃1 : {q : ℚ} {{_ : q ≄ 0}} → q / q ≃ 1
q/q≃1 {q} =
  begin
    q / q
  ≃⟨⟩
    q * q ⁻¹
  ≃⟨ AA.inv ⟩
    1
  ∎
