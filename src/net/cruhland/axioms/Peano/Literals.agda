open import Agda.Builtin.Nat as Nat using (Nat)
open import net.cruhland.axioms.Cast as Cast using (_As_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)

module net.cruhland.axioms.Peano.Literals (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; step; zero)

  private
    ℕ-from-Nat : Nat As ℕ
    ℕ-from-Nat = Cast.As-intro ℕ-from-Nat₀
      where
        ℕ-from-Nat₀ : Nat → ℕ
        ℕ-from-Nat₀ Nat.zero = zero
        ℕ-from-Nat₀ (Nat.suc n) = step (ℕ-from-Nat₀ n)

  instance
    any-from-Nat : {A : Set} {{_ : ℕ As A}} → Nat As A
    any-from-Nat = Cast.via ℕ {{ℕ-from-Nat}}
