import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; const)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using (⊤; ¬_; contra)

module net.cruhland.models.Integers.Negation (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.Equality PA as ℤ≃ using (≃ᶻ-intro)

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = record { -_ = λ { (a — b) → b — a } }

  negative : FromNeg.Negative ℤ
  negative =
    record { Constraint = λ _ → ⊤ ; fromNeg = λ n → - Literals.fromNat n }

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
      neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} (≃ᶻ-intro a₁⁺+a₂⁻≃a₂⁺+a₁⁻) =
          ≃ᶻ-intro a₁⁻+a₂⁺≃a₂⁻+a₁⁺
        where
          a₁⁻+a₂⁺≃a₂⁻+a₁⁺ =
            begin
              a₁⁻ + a₂⁺
            ≃⟨ AA.comm ⟩
              a₂⁺ + a₁⁻
            ≃˘⟨ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              a₁⁺ + a₂⁻
            ≃⟨ AA.comm ⟩
              a₂⁻ + a₁⁺
            ∎

  +-inverseᴸ : AA.Inverse AA.handᴸ (λ x → - x) (const ⊤) _+_ 0
  +-inverseᴸ = AA.inverse +-invᴸ
    where
      +-invᴸ : {x : ℤ} → - x + x ≃ 0
      +-invᴸ {x⁺ — x⁻} = ≃ᶻ-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
        where
          [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
            begin
              (x⁻ + x⁺) + 0
            ≃⟨ AA.comm ⟩
              0 + (x⁻ + x⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              0 + (x⁺ + x⁻)
            ∎

  +-inverseᴿ : AA.Inverse AA.handᴿ (λ x → - x) (const ⊤) _+_ 0
  +-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃ᶻ-intro refl

instance
  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = AA.subst₂

sub-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = AA.subst₂ ∘ AA.subst₁

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ AA.ident ⟩
    a + 0
  ≃˘⟨ AA.subst₂ AA.invᴿ ⟩
    a + (b - b)
  ≃⟨ AA.subst₂ AA.comm ⟩
    a + (- b + b)
  ≃˘⟨ AA.assoc ⟩
    a - b + b
  ≃⟨ AA.subst₂ a-b≃c ⟩
    c + b
  ≃⟨ AA.comm ⟩
    b + c
  ∎
