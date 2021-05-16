open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.MultiplicationImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.BaseImpl PA using (_—_; ℤ)

instance
  star : Op.Star ℤ
  star = Op.star _*₀_
    where
      _*₀_ : ℤ → ℤ → ℤ
      (a⁺ — a⁻) *₀ (b⁺ — b⁻) = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)
