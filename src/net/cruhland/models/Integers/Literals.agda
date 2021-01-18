open import Agda.Builtin.Nat using (Nat)
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Literals as Literals

module net.cruhland.models.Integers.Literals (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Integers.Base PA as Base using (ℤ)
open import net.cruhland.models.Logic using (⊤)

instance
  private
    from-Nat : Nat As ℤ
    from-Nat = Cast.via ℕ

  number : Literals.Number ℤ
  number = record { Constraint = λ _ → ⊤ ; fromNat = _as ℤ }
