open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Data.Unit using (⊤)
open import Function using (const)
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Literals
  (LB : LogicBundle)
  (PB : PeanoBundle LB) where
  open PeanoBundle PB

  fromNat : Nat.Nat → {{_ : ⊤}} → ℕ
  fromNat Nat.zero = zero
  fromNat (Nat.suc n) = step (fromNat n)

  instance
    number : Number ℕ
    number = record { Constraint = const ⊤ ; fromNat = fromNat }
