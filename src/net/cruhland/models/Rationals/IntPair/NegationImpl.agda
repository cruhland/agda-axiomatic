open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.NegationImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

-₀_ : ℚ → ℚ
-₀ (q↑ // q↓) = (- q↑) // q↓

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = Op.dashᴸ -₀_
