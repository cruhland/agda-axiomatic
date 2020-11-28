open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.Multiplication.Base
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)

instance
  star : Op.Star ℤ
  star = record { _*_ = _*₀_ }
    where
      infixl 7 _*₀_
      _*₀_ : ℤ → ℤ → ℤ
      a⁺ — a⁻ *₀ b⁺ — b⁻ = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)
