-- Needed for positive integer literals (typeclass)
open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.Nat using (Nat)
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Rationals.Base (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ; ≃ᶻ-intro)

record ℚ : Set where
  constructor _//_⟨_⟩
  field
    n d : ℤ
    d≄0 : d ≄ 0

infixl 8 _//_
_//_ : (n d : ℤ) {{_ : False (d ≃? 0)}} → ℚ
n // d = n // d ⟨ ≄-derive ⟩

_//1 : ℤ → ℚ
a //1 = a // 1 ⟨ ℕ.step≄zero ∘ AA.inject ⟩

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = record { cast = _//1 }

  from-ℕ : ℕ As ℚ
  from-ℕ = Cast.transitive {B = ℤ}

  private
    from-Nat : Nat As ℚ
    from-Nat = Cast.transitive {B = ℕ}

  number : Number ℚ
  number = record { Constraint = λ _ → ⊤ ; fromNat = _as ℚ }
