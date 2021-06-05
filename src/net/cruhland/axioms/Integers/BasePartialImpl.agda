open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.BasePartialImpl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)

record BaseProperties : Set₁ where
  field
    ℤ : Set
    {{eq}} : Eq ℤ
    {{from-ℕ}} : ℕ As ℤ

  instance
    from-Nat : Nat As ℤ
    from-Nat = Cast.via ℕ

    nat-literal : FromNatLiteral ℤ
    nat-literal = nat-literal-from-cast

  fromNatLiteral≃casts : ∀ n → fromNatLiteral n ≃ (n as ℕ as ℤ)
  fromNatLiteral≃casts n = Eq.refl
