open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contrapositive)

module net.cruhland.models.Rationals.IntPair.ReciprocalImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

_⁻¹₀ : (q : ℚ) {{_ : q ≄ⁱ 0}} → ℚ
_⁻¹₀ (q↑ // q↓) {{q≄ⁱ0}} = (q↓ // q↑) {{contrapositive ℚB.q≃0-from-q↑≃0 q≄ⁱ0}}

instance
  supNegOne : Op.SupNegOne ℚ (_≄ⁱ 0)
  supNegOne = Op.supNegOne _⁻¹₀
