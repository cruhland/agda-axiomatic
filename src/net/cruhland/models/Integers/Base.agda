-- Needed for natural number literals
import Agda.Builtin.FromNat
open import net.cruhland.axioms.Cast using (_As_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for ⊤ instance for natural number literals
import net.cruhland.models.Logic

module net.cruhland.models.Integers.Base (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)

infix 9 _—_
record ℤ : Set where
  constructor _—_
  field
    pos neg : ℕ

instance
  from-ℕ : ℕ As ℤ
  from-ℕ = record { cast = λ n → n — 0 }
