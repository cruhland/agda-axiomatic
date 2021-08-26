import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.NegationPartialImplBase
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private
  module RationalPredefs (QB : Base) (QA : Addition QB) where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public

record NegationBase (QB : Base) (QA : Addition QB) : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{neg-dash}} : Op.Dashᴸ ℚ
    {{neg-substitutive}} : AA.Substitutive₁ {A = ℚ} -_ _≃_ _≃_
    {{+-inverse}} : AA.Inverse² {A = ℚ} (AA.tc₁ λ q → - q) _+_ 0

  instance
    sub-dash : Op.Dash₂ ℚ
    sub-dash = Op.subtraction

    sub-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _-_ _≃_ _≃_
    sub-substitutiveᴸ = AA.substitutive₂ sub-substᴸ
      where
        sub-substᴸ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → p₁ - q ≃ p₂ - q
        sub-substᴸ p₁≃p₂ = AA.subst₂ {A = ℚ} {_⊙_ = AA.tc₂ _+_} p₁≃p₂

    sub-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _-_ _≃_ _≃_
    sub-substitutiveᴿ = AA.substitutive₂ sub-substᴿ
      where
        sub-substᴿ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → q - p₁ ≃ q - p₂
        sub-substᴿ p₁≃p₂ = AA.subst₂ (AA.subst₁ p₁≃p₂)

    sub-substitutive : AA.Substitutive² _-_ _≃_ _≃_
    sub-substitutive = AA.substitutive² {A = ℚ}

  sub-defn : {p q : ℚ} → p - q ≃ p + (- q)
  sub-defn = Eq.refl

  sub-negᴿ : {p q : ℚ} → p - (- q) ≃ p + q
  sub-negᴿ {p} {q} =
    begin
      p - (- q)
    ≃⟨⟩
      p + (- (- q))
    ≃⟨ AA.subst₂ AA.inv-involutive ⟩
      p + q
    ∎

  sub-same : {q : ℚ} → q - q ≃ 0
  sub-same {q} =
    begin
      q - q
    ≃⟨⟩
      q + - q
    ≃⟨ AA.inv ⟩
      0
    ∎

  p≃q-from-p-q≃0 : {p q : ℚ} → p - q ≃ 0 → p ≃ q
  p≃q-from-p-q≃0 {p} {q} p-q≃0 =
    begin
      p
    ≃˘⟨ AA.ident ⟩
      p + 0
    ≃˘⟨ AA.subst₂ AA.inv ⟩
      p + (- q + q)
    ≃˘⟨ AA.assoc ⟩
      (p + - q) + q
    ≃⟨⟩
      (p - q) + q
    ≃⟨ AA.subst₂ p-q≃0 ⟩
      0 + q
    ≃⟨ AA.ident ⟩
      q
    ∎
