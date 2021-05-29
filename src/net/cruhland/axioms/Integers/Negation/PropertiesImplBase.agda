import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl using (NegationBase)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_; const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.Negation.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (NB : NegationBase PA ZB ZP Z+)
  where

private module ℕ = PeanoArithmetic PA
private module ℤ+ = Addition Z+
open Base ZB using (ℤ)

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

  private
    sub-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _-_ _≃_ _≃_
    sub-substitutiveᴸ = AA.substitutive₂ sub-substᴸ
      where
        sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
        sub-substᴸ =
          AA.subst₂ {{r = AA.Substitutive².substitutiveᴸ ℤ+.+-substitutive}}

    sub-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _-_ _≃_ _≃_
    sub-substitutiveᴿ = AA.substitutive₂ sub-substᴿ
      where
        sub-substᴿ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → b - a₁ ≃ b - a₂
        sub-substᴿ = AA.subst₂ ∘ AA.subst₁

  sub-substitutive : AA.Substitutive² _-_ _≃_ _≃_
  sub-substitutive = AA.substitutive²

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ AA.ident ⟩
    0 + a
  ≃˘⟨ AA.subst₂ AA.inv ⟩
    (b - b) + a
  ≃⟨ AA.assoc ⟩
    b + (- b + a)
  ≃⟨ AA.subst₂ AA.comm ⟩
    b + (a - b)
  ≃⟨ AA.subst₂ a-b≃c ⟩
    b + c
  ∎
