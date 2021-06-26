import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.NegationPartialImpl
  (PA : PeanoArithmetic) (ZB : Base PA) (Z+ : Addition PA ZB) where

private module ℤ+ = Addition Z+
open Base ZB using (ℤ)

record NegationProperties : Set₁ where
  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
    {{neg-inverse}} : AA.Inverse² {A = ℤ} -_ (const ⊤) _+_ 0

  instance
    neg-literal : FromNegLiteral ℤ
    neg-literal = FromNegLiteral-intro (λ n → - (fromNatLiteral n))

  neg-literal≃nat-literal : (n : Nat) → fromNegLiteral n ≃ - (fromNatLiteral n)
  neg-literal≃nat-literal n = Eq.refl

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

  instance
    sub-dash : Op.Dash₂ ℤ
    sub-dash = Op.subtraction

  sub-defn : {a b : ℤ} → a - b ≃ a + (- b)
  sub-defn = Eq.refl

  instance
    private
      sub-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _-_ _≃_ _≃_
      sub-substitutiveᴸ = AA.substitutive₂ sub-substᴸ
        where
          sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
          sub-substᴸ {a₁} {a₂} {b} a₁≃a₂ =
            begin
              a₁ - b
            ≃⟨⟩
              a₁ + (- b)
            ≃⟨ AA.subst₂
                 {{r = AA.Substitutive².substitutiveᴸ ℤ+.+-substitutive}}
                 a₁≃a₂ ⟩
              a₂ + (- b)
            ≃⟨⟩
              a₂ - b
            ∎

      sub-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _-_ _≃_ _≃_
      sub-substitutiveᴿ = AA.substitutive₂ sub-substᴿ
        where
          sub-substᴿ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → b - a₁ ≃ b - a₂
          sub-substᴿ {a₁} {a₂} {b} a₁≃a₂ =
            begin
              b - a₁
            ≃⟨⟩
              b + (- a₁)
            ≃⟨ AA.subst₂ (AA.subst₁ a₁≃a₂) ⟩
              b + (- a₂)
            ≃⟨⟩
              b - a₂
            ∎

    sub-substitutive : AA.Substitutive² _-_ _≃_ _≃_
    sub-substitutive = AA.substitutive²

  sub-same≃zero : {a : ℤ} → a - a ≃ 0
  sub-same≃zero = AA.inv

  ≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
  ≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
    begin
      a
    ≃˘⟨ AA.ident ⟩
      0 + a
    ≃˘⟨ AA.subst₂ sub-same≃zero ⟩
      (b - b) + a
    ≃⟨ AA.assoc ⟩
      b + (- b + a)
    ≃⟨ AA.subst₂ AA.comm ⟩
      b + (a - b)
    ≃⟨ AA.subst₂ a-b≃c ⟩
      b + c
    ∎
