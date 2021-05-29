open import Agda.Builtin.Nat as Nat using (Nat)
open import net.cruhland.axioms.Cast as Cast using (_As_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Literals (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; step; zero)

  instance
    from-Nat : Nat As ℕ
    from-Nat = Cast.As-intro from-Nat₀
      where
        from-Nat₀ : Nat → ℕ
        from-Nat₀ Nat.zero = zero
        from-Nat₀ (Nat.suc n) = step (from-Nat₀ n)

    nat-literal : FromNatLiteral Nat
    nat-literal = FromNatLiteral-intro (λ n → n)

    from-literal : FromNatLiteral ℕ
    from-literal = nat-literal-from-cast
