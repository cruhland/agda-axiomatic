import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Literals (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; step; zero)

  fromNat : Nat → ℕ
  fromNat Nat.zero = zero
  fromNat (Nat.suc n) = step (fromNat n)

  instance
    natLiteral : FromNatLiteral ℕ
    natLiteral = FromNatLiteral-intro (AA.tc₁ fromNat)
