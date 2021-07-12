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

module net.cruhland.axioms.Integers.NegationPartialImplSub
  (PA : PeanoArithmetic) (ZB : Base PA) (Z+ : Addition PA ZB) where

private module ℤ+ = Addition Z+
open Base ZB using (ℤ)

record SubtractionProperties : Set₁ where
  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
    {{neg-inverse}} : AA.Inverse² {A = ℤ} -_ (const ⊤) _+_ 0
    {{sub-dash}} : Op.Dash₂ ℤ
    sub-defn : {a b : ℤ} → a - b ≃ a + (- b)

  instance
    private
      sub-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _-_ _≃_ _≃_
      sub-substitutiveᴸ = AA.substitutive₂ sub-substᴸ
        where
          sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
          sub-substᴸ {a₁} {a₂} {b} a₁≃a₂ =
            begin
              a₁ - b
            ≃⟨ sub-defn ⟩
              a₁ + (- b)
            ≃⟨ AA.subst₂
                 {{r = AA.Substitutive²ᶜ.substitutiveᴸ ℤ+.+-substitutive}}
                 a₁≃a₂ ⟩
              a₂ + (- b)
            ≃˘⟨ sub-defn ⟩
              a₂ - b
            ∎

      sub-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _-_ _≃_ _≃_
      sub-substitutiveᴿ = AA.substitutive₂ sub-substᴿ
        where
          sub-substᴿ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → b - a₁ ≃ b - a₂
          sub-substᴿ {a₁} {a₂} {b} a₁≃a₂ =
            begin
              b - a₁
            ≃⟨ sub-defn ⟩
              b + (- a₁)
            ≃⟨ AA.subst₂ (AA.subst₁ a₁≃a₂) ⟩
              b + (- a₂)
            ≃˘⟨ sub-defn ⟩
              b - a₂
            ∎

    sub-substitutive : AA.Substitutive² _-_ _≃_ _≃_
    sub-substitutive = AA.substitutive²

  sub-same≃zero : {a : ℤ} → a - a ≃ 0
  sub-same≃zero {a} =
    begin
      a - a
    ≃⟨ sub-defn ⟩
      a + (- a)
    ≃⟨ AA.inv ⟩
      0
    ∎

  ≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
  ≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
    begin
      a
    ≃˘⟨ AA.ident ⟩
      0 + a
    ≃˘⟨ AA.subst₂ sub-same≃zero ⟩
      (b - b) + a
    ≃⟨ AA.subst₂ sub-defn ⟩
      (b + (- b)) + a
    ≃⟨ AA.assoc ⟩
      b + (- b + a)
    ≃⟨ AA.subst₂ AA.comm ⟩
      b + (a + (- b))
    ≃˘⟨ AA.subst₂ sub-defn ⟩
      b + (a - b)
    ≃⟨ AA.subst₂ a-b≃c ⟩
      b + c
    ∎

  ≃ᴿ-+ᴸ-toᴿ : {a b c : ℤ} → a ≃ b + c → a - b ≃ c
  ≃ᴿ-+ᴸ-toᴿ {a} {b} {c} a≃b+c =
    begin
      a - b
    ≃⟨ sub-defn ⟩
      a + (- b)
    ≃⟨ AA.subst₂ a≃b+c ⟩
      b + c + (- b)
    ≃⟨ AA.subst₂ AA.comm ⟩
      c + b + (- b)
    ≃⟨ AA.assoc ⟩
      c + (b + (- b))
    ≃⟨ AA.subst₂ AA.inv ⟩
      c + 0
    ≃⟨ AA.ident ⟩
      c
    ∎

  ≃-from-zero-sub : {a b : ℤ} → a - b ≃ 0 → a ≃ b
  ≃-from-zero-sub {a} {b} a-b≃0 =
    begin
      a
    ≃⟨ ≃ᴸ-subᴿ-toᴸ a-b≃0 ⟩
      b + 0
    ≃⟨ AA.ident ⟩
      b
    ∎
