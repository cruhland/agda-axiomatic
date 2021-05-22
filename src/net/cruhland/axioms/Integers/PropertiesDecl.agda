open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.PropertiesDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Properties (ZB : Base) : Set where
  open Base ZB using (ℤ)

  field
    {{from-literal}} : FromLiteral ℤ
    casts≃fromNat : ∀ n → (n as ℕ as ℤ) ≃ fromNat n
