import Agda.Builtin.FromNat
open import Function using (_∘_)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Logic

module net.cruhland.models.Rationals.Reciprocal (PA : PeanoArithmetic) where

open import net.cruhland.models.Rationals.Base PA as Base using (_//_⟨_⟩; ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using (q≃0)

_⁻¹ : (q : ℚ) {q≄0 : q ≄ 0} → ℚ
_⁻¹ (q↑ // q↓ ⟨ _ ⟩) {q≄0} = q↓ // q↑ ⟨ q≄0 ∘ q≃0 ⟩
