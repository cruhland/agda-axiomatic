import Agda.Builtin.FromNat
open import Function using (_∘_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Logic

module net.cruhland.models.Rationals.Reciprocal (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA as Base using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using
  (_≃₀_; ≃₀-intro; q≃0)

_⁻¹ : {q : ℚ} → q ≄ 0 → ℚ
_⁻¹ {q↑ // q↓ ~ _} q≄0 = q↓ // q↑ ~ q≄0 ∘ q≃0

recip-subst :
  {q₁ q₂ : ℚ} (q₁≄0 : q₁ ≄ 0) (q₂≄0 : q₂ ≄ 0) → q₁ ≃ q₂ → q₁≄0 ⁻¹ ≃ q₂≄0 ⁻¹
recip-subst _ _ = ≃₀-intro ∘ AA.with-comm ∘ sym ∘ _≃₀_.elim
