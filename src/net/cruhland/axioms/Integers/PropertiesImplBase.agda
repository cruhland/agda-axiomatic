open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.PropertiesImplBase
  (PA : PeanoArithmetic) (ZB : Base PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)

instance
  from-Nat : Nat As ℤ
  from-Nat = Cast.via ℕ

  nat-literal : FromNatLiteral ℤ
  nat-literal = nat-literal-from-cast

casts≃fromNatLiteral : ∀ n → (n as ℕ as ℤ) ≃ fromNatLiteral n
casts≃fromNatLiteral n = Eq.refl
