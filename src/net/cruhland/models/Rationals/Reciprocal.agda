import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contrapositive)

module net.cruhland.models.Rationals.Reciprocal
  (PA : PeanoArithmetic) (Z : Integers PA) where

private module ℕ = PeanoArithmetic PA
private module ℤ = Integers Z
open import net.cruhland.models.Rationals.Base PA Z as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA Z as ℚ≃ using (≃₀-intro)
import net.cruhland.models.Rationals.Multiplication PA Z as ℚ*

_⁻¹ : {q : ℚ} → q ≄ 0 → ℚ
_⁻¹ {q↑ // q↓ ~ _} q≄0 = q↓ // q↑ ~ contrapositive ℚ≃.q≃0 q≄0

infixl 7 _/_
_/_ : (p {q} : ℚ) → q ≄ 0 → ℚ
p / q≄0 = p * q≄0 ⁻¹

recip-subst :
  {q₁ q₂ : ℚ} (q₁≄0 : q₁ ≄ 0) (q₂≄0 : q₂ ≄ 0) → q₁ ≃ q₂ → q₁≄0 ⁻¹ ≃ q₂≄0 ⁻¹
recip-subst _ _ = ≃₀-intro ∘ AA.with-comm ∘ Eq.sym ∘ ℚ≃._≃₀_.elim

recip-inverseᴸ : ∀ {q} {q≄0 : q ≄ 0} → q≄0 ⁻¹ * q ≃ 1
recip-inverseᴸ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

recip-inverseᴿ : ∀ {q} {q≄0 : q ≄ 0} → q * q≄0 ⁻¹ ≃ 1
recip-inverseᴿ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

_⁻¹′ : (q : ℚ) {{_ : q ≄ 0}} → ℚ
_⁻¹′ (q↑ // q↓ ~ _) {{q≄0}} = q↓ // q↑ ~ contrapositive ℚ≃.q≃0 q≄0

infixl 7 _/′_
_/′_ : (p q : ℚ) {{_ : q ≄ 0}} → ℚ
p /′ q = p * q ⁻¹′

instance
  recip-substitutiveᶜ : AA.Substitutive₁ᶜ _⁻¹′ _≃_ _≃_
  recip-substitutiveᶜ = AA.substitutive₁ recip-substᶜ
    where
      recip-substᶜ :
        ∀ {q₁ q₂} {{c₁ : q₁ ≄ 0}} {{c₂ : q₂ ≄ 0}} → q₁ ≃ q₂ → q₁ ⁻¹′ ≃ q₂ ⁻¹′
      recip-substᶜ = ≃₀-intro ∘ AA.with-comm ∘ Eq.sym ∘ ℚ≃._≃₀_.elim

  recip′-inverseᴸ : AA.Inverse AA.handᴸ _⁻¹′ _*_ 1
  recip′-inverseᴸ = AA.inverse recip-invᴸ
    where
      recip-invᴸ : ∀ {q} {{_ : q ≄ 0}} → q ⁻¹′ * q ≃ 1
      recip-invᴸ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

  recip′-inverseᴿ : AA.Inverse AA.handᴿ _⁻¹′ _*_ 1
  recip′-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

  recip′-inverse² : AA.Inverse² _⁻¹′ _*_ 1
  recip′-inverse² = AA.inverse²
