import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Integers.NatPair.BaseImpl as BaseImpl

module net.cruhland.models.Integers.NatPair.NegationImpl
  (PA : PeanoArithmetic) where

open BaseImpl PA using (_—_; ℤ)

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = Op.dashᴸ λ { (x⁺ — x⁻) → x⁻ — x⁺ }
