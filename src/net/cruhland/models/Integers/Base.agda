open import net.cruhland.axioms.Cast as Cast using (_As_; As-intro)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

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
  from-ℕ = As-intro λ n → n — 0

  from-Nat : Nat As ℤ
  from-Nat = Cast.via ℕ

  from-literal : FromLiteral ℤ
  from-literal = literal-from-cast
