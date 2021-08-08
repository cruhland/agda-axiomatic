import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplProperties
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
    open Negation QN public
    open Multiplication QM public

record DivisionProperties
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

  instance
    div-ℚ-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _/_ _≃_ _≃_
    div-ℚ-substitutiveᴸ = AA.substitutive₂ /-substᴸ
      where
        /-substᴸ :
          {q₁ q₂ r : ℚ} {{c₁ : r ≄ 0}} {{c₂ : r ≄ 0}} →
          q₁ ≃ q₂ → (q₁ / r) {{c₁}} ≃ (q₂ / r) {{c₂}}
        /-substᴸ {q₁} {q₂} {r} {{c₁}} {{c₂}} q₁≃q₂ =
          begin
            (q₁ / r) {{c₁}}
          ≃⟨ div-ℚ-defn ⟩
            q₁ * (r ⁻¹) {{c₁}}
          ≃⟨ AA.subst₂ q₁≃q₂ ⟩
            q₂ * (r ⁻¹) {{c₁}}
          ≃⟨ AA.substᴿ (AA.subst₁ Eq.refl) ⟩
            q₂ * (r ⁻¹) {{c₂}}
          ≃˘⟨ div-ℚ-defn ⟩
            (q₂ / r) {{c₂}}
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
            - (p / q) {{c₁}}
          ≃⟨ AA.subst₁ div-ℚ-defn ⟩
            - (p * (q ⁻¹) {{c₁}})
          ≃⟨ AA.fnOpCommᴸ ⟩
            - p * (q ⁻¹) {{c₁}}
          ≃⟨ AA.subst₂ (AA.subst₁ Eq.refl) ⟩
            - p * (q ⁻¹) {{c₂}}
          ≃˘⟨ div-ℚ-defn ⟩
            (- p / q) {{c₂}}
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

  _/ᶻ_ : (a b : ℤ) {{_ : b ≄ 0}} → ℚ
  (a /ᶻ b) {{b≄0}} = let instance b:ℚ≃0:ℚ = AA.subst₁ b≄0 in (a as ℚ) / (b as ℚ)

  instance
    div-ℤ : Op.Slash ℤ (_≄ 0) ℚ
    div-ℤ = Op.slash _/ᶻ_

    div-ℤ-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _/_ _≃_ _≃_
    div-ℤ-substitutiveᴸ = AA.substitutive₂ /ᶻ-substᴸ
      where
        /ᶻ-substᴸ :
          {a₁ a₂ b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : b ≄ 0}} →
          a₁ ≃ a₂ → (a₁ / b) {{c₁}} ≃ (a₂ / b) {{c₂}}
        /ᶻ-substᴸ {a₁} {a₂} {b} {{c₁}} {{c₂}} a₁≃a₂ =
          begin
            (a₁ / b) {{c₁}}
          ≃⟨⟩
            ((a₁ as ℚ) / (b as ℚ)) {{AA.subst₁ c₁}}
          ≃⟨ AA.subst₂
               {{r = div-ℚ-substitutiveᴸ}}
               {{c₁ = AA.subst₁ c₁}} {{c₂ = AA.subst₁ c₁}} (AA.subst₁ a₁≃a₂) ⟩
            ((a₂ as ℚ) / (b as ℚ)) {{AA.subst₁ c₁}}
          ≃⟨ AA.subst₂
               {{r = div-ℚ-substitutiveᴸ}}
               {{c₁ = AA.subst₁ c₁}} {{c₂ = AA.subst₁ c₂}} Eq.refl ⟩
            ((a₂ as ℚ) / (b as ℚ)) {{AA.subst₁ c₂}}
          ≃⟨⟩
            (a₂ / b) {{c₂}}
          ∎

    div-ℤ-substitutiveᴿ : AA.Substitutive₂ᶜ AA.handᴿ _/_ _≃_ _≃_
    div-ℤ-substitutiveᴿ = AA.substitutive₂ /ᶻ-substᴿ
      where
        /ᶻ-substᴿ :
          {a₁ a₂ b : ℤ} {{_ : a₁ ≄ 0}} {{_ : a₂ ≄ 0}} →
          a₁ ≃ a₂ → b / a₁ ≃ b / a₂
        /ᶻ-substᴿ {a₁} {a₂} {b} {{a₁≄0}} {{a₂≄0}} a₁≃a₂ =
          let instance
                a₁:ℚ≄0:ℚ = AA.subst₁ a₁≄0
                a₂:ℚ≄0:ℚ = AA.subst₁ a₂≄0
           in begin
                b / a₁
              ≃⟨⟩
                ((b as ℚ) / (a₁ as ℚ))
              ≃⟨ AA.subst₂
                   {{r = div-ℚ-substitutiveᴿ}} {{c₁ = a₁:ℚ≄0:ℚ}}
                   (AA.subst₁ a₁≃a₂) ⟩
                ((b as ℚ) / (a₂ as ℚ))
              ≃⟨⟩
                b / a₂
              ∎

    div-ℤ-substitutive : AA.Substitutive²ᶜ _/_ _≃_ _≃_
    div-ℤ-substitutive = AA.substitutive² {A = ℤ}

    div-ℤ-comm-with-negᴸ : AA.FnOpCommutative AA.handᴸ -_ -_ _/_
    div-ℤ-comm-with-negᴸ = AA.fnOpCommutative /ᶻ-negᴸ
      where
        /ᶻ-negᴸ :
          {a b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : b ≄ 0}} →
          - (a / b) {{c₁}} ≃ ((- a) / b) {{c₂}}
        /ᶻ-negᴸ {a} {b} {{c₁}} {{c₂}} =
          let instance
                c₁:ℚ = AA.subst₁ c₁
                c₂:ℚ = AA.subst₁ c₂
           in begin
                - (a / b) {{c₁}}
              ≃⟨⟩
                - ((a as ℚ) / (b as ℚ)) {{c₁:ℚ}}
              ≃⟨ AA.fnOpCommᴸ ⟩
                ((- (a as ℚ)) / (b as ℚ)) {{c₁:ℚ}}
              ≃⟨ AA.substᴸ Eq.refl ⟩
                ((- (a as ℚ)) / (b as ℚ)) {{c₂:ℚ}}
              ≃˘⟨ AA.subst₂ AA.compat₁ ⟩
                ((- a as ℚ) / (b as ℚ)) {{c₂:ℚ}}
              ≃⟨⟩
                ((- a) / b) {{c₂}}
              ∎

    div-ℤ-comm-with-negᴿ : AA.FnOpCommutative AA.handᴿ -_ -_ _/_
    div-ℤ-comm-with-negᴿ = AA.fnOpCommutative /ᶻ-negᴿ
      where
        /ᶻ-negᴿ :
          {a b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : - b ≄ 0}} → - (a / b) ≃ a / (- b)
        /ᶻ-negᴿ {a} {b} {{b≄0}} {{ -b≄0 }} =
          let b:ℚ≄0:ℚ = AA.subst₁ b≄0
              [-b]:ℚ≄0:ℚ = AA.subst₁ -b≄0
              -[b:ℚ]≄0:ℚ = AA.substᴸ AA.compat₁ [-b]:ℚ≄0:ℚ
          in begin
                - (a / b) {{b≄0}}
              ≃⟨⟩
                - ((a as ℚ) / (b as ℚ)) {{b:ℚ≄0:ℚ}}
              ≃⟨ AA.fnOpCommᴿ {{c₁ = b:ℚ≄0:ℚ}} {{c₂ = -[b:ℚ]≄0:ℚ}} ⟩
                ((a as ℚ) / (- (b as ℚ))) {{ -[b:ℚ]≄0:ℚ }}
              ≃˘⟨ AA.subst₂ {{c₁ = [-b]:ℚ≄0:ℚ}} {{c₂ = -[b:ℚ]≄0:ℚ}} AA.compat₁ ⟩
                ((a as ℚ) / (- b as ℚ)) {{ [-b]:ℚ≄0:ℚ }}
              ≃⟨⟩
                (a / (- b)) {{ -b≄0 }}
              ∎

    div-ℤ-comm-with-neg : AA.FnOpCommutative² -_ -_ _/_
    div-ℤ-comm-with-neg = AA.fnOpCommutative² {B = ℤ}
