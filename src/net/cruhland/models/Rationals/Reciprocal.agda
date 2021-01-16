import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; _≄ⁱ_; ≄ⁱ-elim; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Reciprocal (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as ℚ≃ using (≃₀-intro)
import net.cruhland.models.Rationals.Literals PA as ℚLit
import net.cruhland.models.Rationals.Multiplication PA as ℚ*

_⁻¹ : {q : ℚ} → q ≄ 0 → ℚ
_⁻¹ {q↑ // q↓ ~ _} q≄0 = q↓ // q↑ ~ q≄0 ∘ ℚ≃.q≃0

infixl 7 _/_
_/_ : (p {q} : ℚ) → q ≄ 0 → ℚ
p / q≄0 = p * q≄0 ⁻¹

recip-subst :
  {q₁ q₂ : ℚ} (q₁≄0 : q₁ ≄ 0) (q₂≄0 : q₂ ≄ 0) → q₁ ≃ q₂ → q₁≄0 ⁻¹ ≃ q₂≄0 ⁻¹
recip-subst _ _ = ≃₀-intro ∘ AA.with-comm ∘ sym ∘ ℚ≃._≃₀_.elim

recip-inverseᴸ : ∀ {q} {q≄0 : q ≄ 0} → q≄0 ⁻¹ * q ≃ 1
recip-inverseᴸ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

recip-inverseᴿ : ∀ {q} {q≄0 : q ≄ 0} → q * q≄0 ⁻¹ ≃ 1
recip-inverseᴿ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

_⁻¹′ : (q : ℚ) {{_ : q ≄ⁱ 0}} → ℚ
_⁻¹′ (q↑ // q↓ ~ _) {{q≄ⁱ0}} = q↓ // q↑ ~ (≄ⁱ-elim q≄ⁱ0) ∘ ℚ≃.q≃0

infixl 7 _/′_
_/′_ : (p q : ℚ) {{_ : q ≄ⁱ 0}} → ℚ
p /′ q = p * q ⁻¹′

instance
  recip-substitutiveⁱ : AA.Substitutiveⁱ _⁻¹′ _≃_ _≃_
  recip-substitutiveⁱ = record { substⁱ = recip-substⁱ }
    where
      recip-substⁱ :
        ∀ {q₁ q₂} {{c₁ : q₁ ≄ⁱ 0}} {{c₂ : q₂ ≄ⁱ 0}} → q₁ ≃ q₂ → q₁ ⁻¹′ ≃ q₂ ⁻¹′
      recip-substⁱ = ≃₀-intro ∘ AA.with-comm ∘ sym ∘ ℚ≃._≃₀_.elim

  recip′-inverseᴸ : AA.Inverseᴸ _⁻¹′
  recip′-inverseᴸ = AA.inverseᴸ recip-invᴸ
    where
      recip-invᴸ : ∀ {q} {{_ : q ≄ⁱ 0}} → q ⁻¹′ * q ≃ 1
      recip-invᴸ {q↑ // q↓ ~ _} = ℚ≃.q≃1 AA.comm

  recip′-inverseᴿ : AA.Inverseᴿ _⁻¹′
  recip′-inverseᴿ = AA.inverseᴿ-from-inverseᴸ
