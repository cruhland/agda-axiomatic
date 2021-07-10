import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_value_)
open import net.cruhland.axioms.Eq using (_≄_; ≄ⁱ-elim; ≄ⁱ-intro)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.AdditionImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

_+₀_ : ℚ → ℚ → ℚ
(p↑ // p↓) +₀ (q↑ // q↓) =
  let p↓≄0 = (p↓ ≄ 0) value ≄ⁱ-elim
      q↓≄0 = (q↓ ≄ 0) value ≄ⁱ-elim
      p↓q↓≄0 = AA.nonzero-prod p↓≄0 q↓≄0
      instance p↓q↓≄ⁱ0 = ≄ⁱ-intro p↓q↓≄0
   in (p↑ * q↓ + p↓ * q↑) // (p↓ * q↓)

instance
  plus : Op.Plus ℚ
  plus = Op.plus _+₀_
