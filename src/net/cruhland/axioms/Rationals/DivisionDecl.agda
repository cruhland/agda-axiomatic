import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)
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

module DivisionPredefs
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    where
  private open module ℚ = RationalPredefs QB QA QN QM QR using (ℚ)

  div-ℤ-type : Set
  div-ℤ-type = Op.Slash ℤ (_≄ 0) ℚ

  record Fraction (q : ℚ) {{_ : div-ℤ-type}} : Set where
    constructor fraction-intro
    field
      {a b} : ℤ
      {{b≄0}} : b ≄ 0
      q≃a/b : q ≃ a / b

record Division
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    : Set where
  private open module ℚ = RationalPredefs QB QA QN QM QR using (ℚ)
  open DivisionPredefs QB QA QN QM QR public

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    div-ℚ-defn : {p q : ℚ} {{_ : q ≄ 0}} → p / q ≃ p * q ⁻¹
    div-ℚ-subst-proof :
      {p q : ℚ} {{q≄0₁ q≄0₂ : q ≄ 0}} → (p / q) {{q≄0₁}} ≃ (p / q) {{q≄0₂}}
    q/q≃1 : {q : ℚ} {{_ : q ≄ 0}} → q / q ≃ 1

    {{div-ℚ-substitutive}} : AA.Substitutive²ᶜ {A = ℚ} _/_ _≃_ _≃_
    {{div-ℚ-comm-with-neg}} : AA.FnOpCommutative² -_ -_ _/_
    {{div-ℚ-absorptiveᴸ}} : AA.Absorptive AA.handᴸ _/_
    {{div-ℚ-distributive-+ᴿ}} : AA.Distributive AA.handᴿ _/_ _+_
    {{div-ℚ-cancellative-*}} :
      AA.Cancellative²ᶜ (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0) (_≄ 0)

    +-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) + (r / s) ≃ (p * s + q * r) / (q * s)
    *-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) * (r / s) ≃ (p * r) / (q * s)

    {{div-ℤ}} : div-ℤ-type
    div-ℤ-defn :
      {a b : ℤ} {{b≄0 : b ≄ 0}} →
      let instance b:ℚ≄0:ℚ = AA.subst₁ b≄0 in a / b ≃ (a as ℚ) / (b as ℚ)
    div-ℤ-subst-proof :
      {a b : ℤ} {{b≄0₁ b≄0₂ : b ≄ 0}} → (a / b) {{b≄0₁}} ≃ (a / b) {{b≄0₂}}

    {{div-ℤ-substitutive}} : AA.Substitutive²ᶜ {A = ℤ} _/_ _≃_ _≃_
    {{div-ℤ-comm-with-neg}} : AA.FnOpCommutative² {B = ℤ} -_ -_ _/_
    {{div-ℤ-absorptiveᴸ}} : AA.Absorptive AA.handᴸ {A = ℤ} _/_
    {{div-ℤ-cancellative-*}} :
      AA.Cancellative²ᶜ {A = ℤ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0) (_≄ 0)

    a≃0-from-a/b≃0 : {a b : ℤ} {{_ : b ≄ 0}} → a / b ≃ 0 → a ≃ 0
    a/a≃1 : {a : ℤ} {{_ : a ≄ 0}} → a / a ≃ 1
    fraction : (q : ℚ) → Fraction q

    +-div-ℤ :
      {a b c d : ℤ} {{b≄0 : b ≄ 0}} {{d≄0 : d ≄ 0}} →
      let instance bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
       in (a / b) + (c / d) ≃ (a * d + b * c) / (b * d)
    *-div-ℤ :
      {a b c d : ℤ} {{b≄0 : b ≄ 0}} {{d≄0 : d ≄ 0}} →
      let instance bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
       in (a / b) * (c / d) ≃ (a * c) / (b * d)
