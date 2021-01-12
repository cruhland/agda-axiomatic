import Agda.Builtin.Nat as Nat
open import net.cruhland.axioms.Cast using (_As_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Peano.Literals (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; step; zero)

  fromNat : Nat.Nat → {{_ : ⊤}} → ℕ
  fromNat Nat.zero = zero
  fromNat (Nat.suc n) = step (fromNat n)

  instance
    number : Literals.Number ℕ
    number = record { Constraint = const ⊤ ; fromNat = fromNat }

    from-Nat : Nat.Nat As ℕ
    from-Nat = record { cast = λ n → fromNat n }
