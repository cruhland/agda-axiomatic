import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_; _value_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.axioms.Integers.BasePartialImpl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)

record BaseProperties : Set₁ where
  field
    ℤ : Set
    {{eq}} : Eq ℤ
    {{from-ℕ}} : ℕ As ℤ
    {{from-ℕ-injective}} : AA.Injective {A = ℕ} (_as ℤ) _≃_ _≃_

  instance
    from-Nat : Nat As ℤ
    from-Nat = Cast.via ℕ

    nat-literal : FromNatLiteral ℤ
    nat-literal = nat-literal-from-cast

    1≄0 : (ℤ value 1) ≄ 0
    1≄0 = Eq.≄-intro λ 1:ℤ≃0:ℤ →
      let s0≃0 = AA.inject 1:ℤ≃0:ℤ
       in s0≃0 ↯ ℕ.step≄zero

  fromNatLiteral≃casts : ∀ n → fromNatLiteral n ≃ (n as ℕ as ℤ)
  fromNatLiteral≃casts n = Eq.refl
