open import Agda.Builtin.Nat using (Nat)
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Rationals.Literals (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Rationals.Base PA as Base using (ℚ)

instance
  private
    from-Nat : Nat As ℚ
    from-Nat = Cast.transitive {B = ℕ}

  number : Literals.Number ℚ
  number = record { Constraint = λ _ → ⊤ ; fromNat = _as ℚ }
