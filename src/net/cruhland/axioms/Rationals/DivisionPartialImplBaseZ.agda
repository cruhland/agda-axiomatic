import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplBaseZ
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)

private
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      where
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public

record DivisionBaseZ
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    : Set where
  private open module ℚ = RationalPredefs QB QA QN QM using (ℚ)

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    {{div-ℚ-substitutive}} : AA.Substitutive²ᶜ {A = ℚ} _/_ _≃_ _≃_
    q/q≃1 : {q : ℚ} {{_ : q ≄ 0}} → q / q ≃ 1
    +-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) + (r / s) ≃ (p * s + q * r) / (q * s)
    *-div-ℚ :
      {p q r s : ℚ} {{q≄0 : q ≄ 0}} {{s≄0 : s ≄ 0}} →
      let instance qs≄0 = AA.nonzero-prod {{a≄0 = q≄0}} {{s≄0}}
       in (p / q) * (r / s) ≃ (p * r) / (q * s)

  _/ᶻ_ : (a b : ℤ) {{_ : b ≄ 0}} → ℚ
  (a /ᶻ b) {{b≄0}} = let instance b:ℚ≃0:ℚ = AA.subst₁ b≄0 in (a as ℚ) / (b as ℚ)

  instance
    div-ℤ : Op.Slash ℤ (_≄ 0) ℚ
    div-ℤ = Op.slash _/ᶻ_

  div-ℤ-defn :
    {a b : ℤ} {{b≄0 : b ≄ 0}} →
    let instance b:ℚ≄0:ℚ = AA.subst₁ b≄0 in a / b ≃ (a as ℚ) / (b as ℚ)
  div-ℤ-defn = Eq.refl

  *-div-ℤ :
    {a b c d : ℤ} {{b≄0 : b ≄ 0}} {{d≄0 : d ≄ 0}} →
    let instance bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
     in (a / b) * (c / d) ≃ (a * c) / (b * d)
  *-div-ℤ {a} {b} {c} {d} {{b≄0}} {{d≄0}} =
    let instance
          bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
          b:ℚ≄0:ℚ = AA.subst₁ b≄0
          d:ℚ≄0:ℚ = AA.subst₁ d≄0
          b:ℚ*d:ℚ≄0:ℚ = AA.nonzero-prod {{a≄0 = b:ℚ≄0:ℚ}} {{d:ℚ≄0:ℚ}}
          bd:ℚ≄0:ℚ = AA.subst₁ bd≄0
     in begin
          (a / b) * (c / d)
        ≃⟨⟩
          (((a as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ}}) * ((c as ℚ) / (d as ℚ))
        ≃⟨ *-div-ℚ ⟩
          ((a as ℚ) * (c as ℚ)) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
          (a * c as ℚ) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
          (a * c as ℚ) / (b * d as ℚ)
        ≃⟨⟩
          (a * c) / (b * d)
        ∎

  +-div-ℤ :
    {a b c d : ℤ} {{b≄0 : b ≄ 0}} {{d≄0 : d ≄ 0}} →
    let instance bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
     in (a / b) + (c / d) ≃ (a * d + b * c) / (b * d)
  +-div-ℤ {a} {b} {c} {d} {{b≄0}} {{d≄0}} =
    let instance
          bd≄0 = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
          b:ℚ≄0:ℚ = AA.subst₁ b≄0
          d:ℚ≄0:ℚ = AA.subst₁ d≄0
          bd:ℚ≄0:ℚ = AA.subst₁ bd≄0
          b:ℚ*d:ℚ≄0:ℚ = AA.nonzero-prod {{a≄0 = b:ℚ≄0:ℚ}} {{d:ℚ≄0:ℚ}}
     in begin
          (a / b) + (c / d)
        ≃⟨⟩
          ((a as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ}} + ((c as ℚ) / (d as ℚ)) {{d:ℚ≄0:ℚ}}
        ≃⟨ +-div-ℚ ⟩
          ((a as ℚ) * (d as ℚ) + (b as ℚ) * (c as ℚ)) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.compat₂) ⟩
          ((a * d as ℚ) + (b as ℚ) * (c as ℚ)) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.compat₂) ⟩
          ((a * d as ℚ) + (b * c as ℚ)) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
          (a * d + b * c as ℚ) / ((b as ℚ) * (d as ℚ))
        ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
          (a * d + b * c as ℚ) / (b * d as ℚ)
        ≃⟨⟩
          (a * d + b * c) / (b * d)
        ∎

  a/a≃1 : {a : ℤ} {{_ : a ≄ 0}} → a / a ≃ 1
  a/a≃1 {a} {{a≄0}} =
    let instance
          a:ℚ≃0:ℚ = AA.subst₁ a≄0
    in begin
         a / a
       ≃⟨⟩
         (a as ℚ) / (a as ℚ)
       ≃⟨ q/q≃1 ⟩
         1
       ∎
