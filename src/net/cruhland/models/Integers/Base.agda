open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.Base (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)

infix 9 _—_
record ℤ : Set where
  constructor _—_
  field
    pos neg : ℕ
