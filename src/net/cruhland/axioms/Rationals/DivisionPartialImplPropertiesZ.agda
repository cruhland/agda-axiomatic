import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _*_; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplPropertiesZ
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)

private
  open module ℤ = Integers Z using (ℤ)
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public

record DivisionPropertiesZ
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    : Set where
  private
    open module ℚ = RationalPredefs QB QA QN QM using (ℚ)

  field
    {{div-ℚ}} : Op.Slash ℚ (_≄ 0) ℚ
    {{div-ℚ-substitutive}} : AA.Substitutive²ᶜ _/_ _≃_ _≃_
    {{div-ℚ-comm-with-neg}} : AA.FnOpCommutative² -_ -_ _/_
    {{div-ℚ-absorptiveᴸ}} : AA.Absorptive AA.handᴸ _/_
    {{div-ℚ-cancellative-*}} :
      AA.Cancellative²ᶜ (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0) (_≄ 0)

    {{div-ℤ}} : Op.Slash ℤ (_≄ 0) ℚ
    div-ℤ-defn :
      {a b : ℤ} {{b≄0 : b ≄ 0}} →
      let instance b:ℚ≄0:ℚ = AA.subst₁ b≄0 in a / b ≃ (a as ℚ) / (b as ℚ)

  instance
    div-ℤ-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _/_ _≃_ _≃_
    div-ℤ-substitutiveᴸ = AA.substitutive₂ /-substᴸ
      where
        /-substᴸ :
          {a₁ a₂ b : ℤ} {{b≄0₁ : b ≄ 0}} {{b≄0₂ : b ≄ 0}} →
          a₁ ≃ a₂ → (a₁ / b) {{b≄0₁}} ≃ (a₂ / b) {{b≄0₂}}
        /-substᴸ {a₁} {a₂} {b} {{b≄0₁}} {{b≄0₂}} a₁≃a₂ =
          let instance
                b:ℚ≄0:ℚ₁ = AA.subst₁ b≄0₁
                b:ℚ≄0:ℚ₂ = AA.subst₁ b≄0₂
           in begin
                a₁ / b
              ≃⟨ div-ℤ-defn ⟩
                ((a₁ as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ₁}}
              ≃⟨ AA.substᴿ Eq.refl ⟩
                ((a₁ as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ₂}}
              ≃⟨ AA.subst₂ (AA.subst₁ a₁≃a₂) ⟩
                (a₂ as ℚ) / (b as ℚ)
              ≃˘⟨ div-ℤ-defn ⟩
                (a₂ / b)
              ∎

    div-ℤ-substitutiveᴿ : AA.Substitutive₂ᶜ AA.handᴿ _/_ _≃_ _≃_
    div-ℤ-substitutiveᴿ = AA.substitutive₂ /-substᴿ
      where
        /-substᴿ :
          {a₁ a₂ b : ℤ} {{_ : a₁ ≄ 0}} {{_ : a₂ ≄ 0}} →
          a₁ ≃ a₂ → b / a₁ ≃ b / a₂
        /-substᴿ {a₁} {a₂} {b} {{a₁≄0}} {{a₂≄0}} a₁≃a₂ =
          let instance
                a₁:ℚ≄0:ℚ = AA.subst₁ a₁≄0
                a₂:ℚ≄0:ℚ = AA.subst₁ a₂≄0
           in begin
                b / a₁
              ≃⟨ div-ℤ-defn ⟩
                ((b as ℚ) / (a₁ as ℚ)) {{a₁:ℚ≄0:ℚ}}
              ≃⟨ AA.subst₂ (AA.subst₁ a₁≃a₂) ⟩
                (b as ℚ) / (a₂ as ℚ)
              ≃˘⟨ div-ℤ-defn ⟩
                b / a₂
              ∎

    div-ℤ-substitutive : AA.Substitutive²ᶜ _/_ _≃_ _≃_
    div-ℤ-substitutive = AA.substitutive² {A = ℤ}

    div-ℤ-comm-with-negᴸ : AA.FnOpCommutative AA.handᴸ -_ -_ _/_
    div-ℤ-comm-with-negᴸ = AA.fnOpCommutative /-negᴸ
      where
        /-negᴸ :
          {a b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : b ≄ 0}} →
          - (a / b) {{c₁}} ≃ ((- a) / b) {{c₂}}
        /-negᴸ {a} {b} {{c₁}} {{c₂}} =
          let instance
                c₁:ℚ = AA.subst₁ c₁
                c₂:ℚ = AA.subst₁ c₂
           in begin
                - (a / b)
              ≃⟨ AA.subst₁ div-ℤ-defn ⟩
                - ((a as ℚ) / (b as ℚ)) {{c₁:ℚ}}
              ≃⟨ AA.fnOpCommᴸ ⟩
                ((- (a as ℚ)) / (b as ℚ)) {{c₂:ℚ}}
              ≃˘⟨ AA.subst₂ AA.compat₁ ⟩
                (- a as ℚ) / (b as ℚ)
              ≃˘⟨ div-ℤ-defn ⟩
                (- a) / b
              ∎

    div-ℤ-comm-with-negᴿ : AA.FnOpCommutative AA.handᴿ -_ -_ _/_
    div-ℤ-comm-with-negᴿ = AA.fnOpCommutative {A = ℚ} /-negᴿ
      where
        /-negᴿ :
          {a b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : - b ≄ 0}} → - (a / b) ≃ a / (- b)
        /-negᴿ {a} {b} {{b≄0}} {{ -b≄0 }} =
          let instance
                b:ℚ≄0:ℚ = AA.subst₁ b≄0
                [-b]:ℚ≄0:ℚ = AA.subst₁ -b≄0
                -[b:ℚ]≄0:ℚ = AA.substᴸ AA.compat₁ [-b]:ℚ≄0:ℚ
           in begin
                - (a / b)
              ≃⟨ AA.subst₁ div-ℤ-defn ⟩
                - ((a as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ}}
              ≃⟨ AA.fnOpCommᴿ ⟩
                (a as ℚ) / (- (b as ℚ))
              ≃˘⟨ AA.subst₂ AA.compat₁ ⟩
                (a as ℚ) / (- b as ℚ)
              ≃˘⟨ div-ℤ-defn ⟩
                a / (- b)
              ∎

    div-ℤ-comm-with-neg : AA.FnOpCommutative² -_ -_ _/_
    div-ℤ-comm-with-neg = AA.fnOpCommutative² {B = ℤ}

    div-ℤ-absorptiveᴸ : AA.Absorptive AA.handᴸ _/_
    div-ℤ-absorptiveᴸ = AA.absorptive {-A = ℤ-} 0/b≃0
      where
        0/b≃0 : {b : ℤ} {{_ : b ≄ 0}} → 0 / b ≃ 0
        0/b≃0 {b} {{b≄0}} =
          let instance
                b:ℚ≄0:ℚ = AA.subst₁ b≄0
           in begin
                0 / b
              ≃⟨ div-ℤ-defn ⟩
                (0 as ℚ) / (b as ℚ)
              ≃⟨⟩
                0 / (b as ℚ)
              ≃⟨ AA.absorb ⟩
                0
              ∎

    div-ℤ-cancellative-*ᴸ :
      AA.Cancellativeᶜ AA.handᴸ {A = ℤ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0)
    div-ℤ-cancellative-*ᴸ = AA.cancellative /-cancel-*ᴸ
      where
        /-cancel-*ᴸ :
          {a : ℤ} {{Ca : a ≄ 0}} {b c : ℤ} {{C~ : c ≄ 0}} {{C≈ : a * c ≄ 0}} →
          (a * b) / (a * c) ≃ b / c
        /-cancel-*ᴸ {a} {{Ca = a≄0}} {b} {c} {{C~ = c≄0}} {{C≈ = ac≄0}} =
          let instance
                a:ℚ≄0:ℚ = AA.subst₁ a≄0
                c:ℚ≄0:ℚ = AA.subst₁ c≄0
                ac:ℚ≄0:ℚ = AA.subst₁ ac≄0
                a:ℚ*c:ℚ≄0:ℚ = AA.nonzero-prod {{a≄0 = a:ℚ≄0:ℚ}} {{c:ℚ≄0:ℚ}}
           in begin
                (a * b) / (a * c)
              ≃⟨ div-ℤ-defn ⟩
                ((a * b as ℚ) / (a * c as ℚ)) {{ac:ℚ≄0:ℚ}}
              ≃⟨ AA.subst₂ AA.compat₂ ⟩
                ((a as ℚ) * (b as ℚ)) / (a * c as ℚ)
              ≃⟨ AA.subst₂ AA.compat₂ ⟩
                ((a as ℚ) * (b as ℚ)) / ((a as ℚ) * (c as ℚ))
              ≃⟨ AA.cancel ⟩
                ((b as ℚ) / (c as ℚ)) {{c:ℚ≄0:ℚ}}
              ≃˘⟨ div-ℤ-defn ⟩
                b / c
              ∎

    div-ℤ-cancellative-*ᴿ :
      AA.Cancellativeᶜ AA.handᴿ {A = ℤ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0)
    div-ℤ-cancellative-*ᴿ = AA.cancelᴿ-from-cancelᴸ-comm₂
      where
        instance ≄0-subst = AA.NeqProperties.≄-substitutive₁ᴸ

    div-ℤ-cancellative-* :
      AA.Cancellative²ᶜ {A = ℤ} (AA.tc₂ _*_) _/_ _/_ _≃_ (_≄ 0) (_≄ 0)
    div-ℤ-cancellative-* = AA.cancellative²
