module net.cruhland.models.Peano.Unary.Full where

open import Data.Nat using (ℕ; _*_; _^_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
import net.cruhland.models.Peano.Unary.Base as UB
import net.cruhland.models.Peano.Unary.Ordering as UO

instance
  star : Op.Star ℕ
  star = Op.star _*_

  *-absorptiveᴸ : AA.Absorptive AA.handᴸ _*_ 0
  *-absorptiveᴸ = AA.absorptive Eq.refl

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_ _≡_ _≡_
  *-substitutiveᴸ = AA.substitutive₂ λ {_ _ b} → PropEq.cong (_* b)

multiplication : Multiplication UB.base UB.sign UB.addition UO.ordering
multiplication = record { *-stepᴸ = λ {n m} → +-comm m (n * m) }

instance
  caret : Op.Caret ℕ
  caret = Op.caret _^_

exponentiation :
    Exponentiation UB.base UB.sign UB.addition UO.ordering multiplication
exponentiation =
  record { ^-zeroᴿ = Eq.refl ; ^-stepᴿ = λ {n m} → *-comm n (n ^ m) }

peanoArithmetic : PeanoArithmetic
peanoArithmetic = record
  { PB = UB.base
  ; PS = UB.sign
  ; PA = UB.addition
  ; PO = UO.ordering
  ; PM = multiplication
  ; PE = exponentiation
  }
