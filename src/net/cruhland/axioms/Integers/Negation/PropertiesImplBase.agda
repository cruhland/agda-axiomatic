import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl using (NegationBase)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_; const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.Negation.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (NB : NegationBase PA ZB Z+)
  where

private module ℕ = PeanoArithmetic PA
private module ℤ+ = Addition Z+
open Base ZB using (ℤ)

instance
  neg-literal : FromNeg.Negative ℤ
  neg-literal = record { Constraint = const ⊤ ; fromNeg = λ n → - (n as ℤ) }

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
  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

  sub-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _-_ _≃_ _≃_
  sub-substitutiveᴸ = AA.substitutive₂ sub-substᴸ
    where
      sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
      sub-substᴸ =
        AA.subst₂ {{r = AA.Substitutive₂².substitutiveᴸ ℤ+.+-substitutive}}

  sub-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _-_ _≃_ _≃_
  sub-substitutiveᴿ = AA.substitutive₂ sub-substᴿ
    where
      sub-substᴿ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → b - a₁ ≃ b - a₂
      sub-substᴿ = AA.subst₂ ∘ AA.subst₁

  sub-substitutive : AA.Substitutive₂² _-_ _≃_ _≃_
  sub-substitutive = AA.substitutive₂²

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ AA.ident ⟩
    0 + a
  ≃˘⟨ AA.subst₂ AA.invᴿ ⟩
    (b - b) + a
  ≃⟨ AA.assoc ⟩
    b + (- b + a)
  ≃⟨ AA.subst₂ AA.comm ⟩
    b + (a - b)
  ≃⟨ AA.subst₂ a-b≃c ⟩
    b + c
  ∎
