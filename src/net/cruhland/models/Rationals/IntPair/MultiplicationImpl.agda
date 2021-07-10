import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_value_)
open import net.cruhland.axioms.Eq using (_≄_; ≄ⁱ-elim; ≄ⁱ-intro)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.MultiplicationImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

_*₀_ : ℚ → ℚ → ℚ
(p↑ // p↓) *₀ (q↑ // q↓) = ((p↑ * q↑) // (p↓ * q↓)) {{AA.nonzero-prodⁱ}}

instance
  star : Op.Star ℚ
  star = Op.star _*₀_
