module net.cruhland.models.Peano.Unary where

open import Data.Nat using (ℕ; _+_; _*_; _^_; zero) renaming (suc to step)
open import Data.Nat.Properties
  using (+-comm; *-comm) renaming (suc-injective to step-inj)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; ≢-sym; trans)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; As-intro)
import net.cruhland.axioms.Eq as Eq
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
import net.cruhland.axioms.Peano.Inspect as Inspect
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.axioms.Sign using (Positive)
open import net.cruhland.models.Function using (_∘_; id)

instance
  ≡-reflexive : Eq.Reflexive _≡_
  ≡-reflexive = Eq.reflexive {A = ℕ} refl

  ≡-symmetric : Eq.Symmetric _≡_
  ≡-symmetric = Eq.symmetric {A = ℕ} sym

  ≡-transitive : Eq.Transitive _≡_
  ≡-transitive = Eq.transitive {A = ℕ} trans

  eq : Eq.Eq ℕ
  eq = Eq.equivalence _≡_

  step-substitutive : AA.Substitutive₁ step _≡_ _≡_
  step-substitutive = AA.substitutive₁ (cong step)

  step-injective : AA.Injective step _≡_ _≡_
  step-injective = AA.injective step-inj

ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (step k)) → ∀ n → P n
ind P Pz Ps zero = Pz
ind P Pz Ps (step n) = ind (P ∘ step) (Ps Pz) Ps n

base : Peano
base = record
  { ℕ = ℕ
  ; zero = zero
  ; step = step
  ; step≄zero = λ ()
  ; ind = ind
  }

module inspect = Inspect base

instance
  default-positivity = inspect.non-zero-positivity

  from-n≄0 : {n : ℕ} → (n ≢ 0) As Positive n
  from-n≄0 = As-intro id

sign : Sign base
sign = record {}

instance
  plus : Op.Plus ℕ
  plus = record { _+_ = _+_ }

  +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_
  +-substitutiveᴸ = AA.substitutive₂ λ {_ _ b} → cong (_+ b)

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity refl

  +-fnOpCommutative-stepᴸ : AA.FnOpCommutative AA.handᴸ step _+_
  +-fnOpCommutative-stepᴸ = AA.fnOpCommutative refl

addition : Addition base sign
addition = record {}

instance
  star : Op.Star ℕ
  star = record { _*_ = _*_ }

  *-absorptiveᴸ : AA.Absorptive AA.handᴸ _*_ 0
  *-absorptiveᴸ = AA.absorptive refl

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_
  *-substitutiveᴸ = AA.substitutive₂ λ {_ _ b} → cong (_* b)

multiplication : Multiplication base sign addition
multiplication = record { *-stepᴸ = λ {n m} → +-comm m (n * m) }

exponentiation : Exponentiation base sign addition multiplication
exponentiation =
  record { _^_ = _^_ ; ^-zeroᴿ = refl ; ^-stepᴿ = λ {n m} → *-comm n (n ^ m) }

peanoArithmetic : PeanoArithmetic
peanoArithmetic = record
  { PB = base
  ; PA = addition
  ; PS = sign
  ; PM = multiplication
  ; PE = exponentiation
  }
