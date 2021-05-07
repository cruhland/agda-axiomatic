open import net.cruhland.axioms.Cast using (_As_)
open import net.cruhland.axioms.Eq using (Eq)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.BaseDecl (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)

record Base : Set₁ where
  field
    ℤ : Set
    {{eq}} : Eq ℤ
    {{from-ℕ}} : ℕ As ℤ
