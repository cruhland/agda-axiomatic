open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
import Data.Unit as Unit
open import Function using (const)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Literals (PB : PeanoBundle) where
  open PeanoBundle PB

  fromNat : Nat.Nat → {{_ : Unit.⊤}} → ℕ
  fromNat Nat.zero = zero
  fromNat (Nat.suc n) = succ (fromNat n)

  instance
    number : Number ℕ
    number = record { Constraint = const Unit.⊤ ; fromNat = fromNat }
