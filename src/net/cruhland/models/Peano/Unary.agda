module net.cruhland.models.Peano.Unary where

open import Data.Nat using (ℕ; _+_; _*_; _^_; zero) renaming (suc to step)
open import Data.Nat.Properties
  using (+-comm; *-comm) renaming (suc-injective to step-inj)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; ≢-sym; trans)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (Eq)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)

ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (step k)) → ∀ n → P n
ind P Pz Ps zero = Pz
ind P Pz Ps (step n) = ind (P ∘ step) (Ps Pz) Ps n

instance
  eq : Eq ℕ
  eq = record
    { _≃_ = _≡_
    ; refl = refl
    ; sym = sym
    ; trans = trans
    }

  step-substitutive : AA.Substitutive₁ step
  step-substitutive = record { subst = cong step }

  step-injective : AA.Injective step
  step-injective = record { inject = step-inj }

base : Peano
base = record
  { ℕ = ℕ
  ; zero = zero
  ; step = step
  ; step≄zero = λ ()
  ; ind = ind
  }

instance
  plus : Op.Plus ℕ
  plus = record { _+_ = _+_ }

  +-substitutiveᴸ : AA.Substitutiveᴸ _+_
  +-substitutiveᴸ = record { substᴸ = λ {_ _ m} → cong (_+ m) }

  +-identityᴸ : AA.Identityᴸ _+_ zero
  +-identityᴸ = record { identᴸ = refl }

  +-commutative-stepᴸ : AA.Commutativeᴸ step _+_
  +-commutative-stepᴸ = record { commᴸ = refl }

addition : Addition base
addition = record {}

instance
  star : Op.Star ℕ
  star = record { _*_ = _*_ }

  *-substitutiveᴸ : AA.Substitutiveᴸ _*_
  *-substitutiveᴸ = record { substᴸ = λ {_ _ m} → cong (_* m) }

  *-absorptiveᴸ : AA.Absorptiveᴸ _*_ zero
  *-absorptiveᴸ = record { absorbᴸ = refl }

multiplication : Multiplication base addition
multiplication = record { *-stepᴸ = λ {n m} → +-comm m (n * m) }

exponentiation : Exponentiation base addition multiplication
exponentiation =
  record { _^_ = _^_ ; ^-zeroᴿ = refl ; ^-stepᴿ = λ {n m} → *-comm n (n ^ m) }

peanoArithmetic : PeanoArithmetic
peanoArithmetic = record
  { PB = base ; PA = addition ; PM = multiplication ; PE = exponentiation }
