module net.cruhland.models.Peano.Unary where

open import Data.Nat using (ℕ; _+_; _*_; _^_; zero) renaming (suc to step)
open import Data.Nat.Properties
  using (+-comm; *-comm) renaming (suc-injective to step-inj)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; ≢-sym; trans)
import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
open import net.cruhland.models.Function using (_∘_)

ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (step k)) → ∀ n → P n
ind P Pz Ps zero = Pz
ind P Pz Ps (step n) = ind (P ∘ step) (Ps Pz) Ps n

instance
  ≡-reflexive : Eq.Reflexive {A = ℕ} _≡_
  ≡-reflexive = record { refl = refl }

  ≡-symmetric : Eq.Symmetric {A = ℕ} _≡_
  ≡-symmetric = record { sym = sym }

  ≡-transitive : Eq.Transitive {A = ℕ} _≡_
  ≡-transitive = record { trans = trans }

  eq : Eq.Eq ℕ
  eq = record { _≃_ = _≡_ }

  step-substitutive : AA.Substitutive₁ step _≡_ _≡_
  step-substitutive = AA.substitutive₁ (cong step)

  step-injective : AA.Injective step _≡_ _≡_
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

  +-substitutiveᴸ : ∀ {m} → AA.Substitutive₁ (_+ m) _≡_ _≡_
  +-substitutiveᴸ {m} = AA.substitutive₁ (cong (_+ m))

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity refl

  +-commutative-stepᴸ : AA.Commutativeᴸ step _+_
  +-commutative-stepᴸ = record { commᴸ = refl }

addition : Addition base
addition = record {}

instance
  star : Op.Star ℕ
  star = record { _*_ = _*_ }

  *-substitutiveᴸ : ∀ {m} → AA.Substitutive₁ (_* m) _≡_ _≡_
  *-substitutiveᴸ {m} = AA.substitutive₁ (cong (_* m))

multiplication : Multiplication base addition
multiplication =
  record { *-isAbsorptiveᴸ = refl ; *-stepᴸ = λ {n m} → +-comm m (n * m) }

exponentiation : Exponentiation base addition multiplication
exponentiation =
  record { _^_ = _^_ ; ^-zeroᴿ = refl ; ^-stepᴿ = λ {n m} → *-comm n (n ^ m) }

peanoArithmetic : PeanoArithmetic
peanoArithmetic = record
  { PB = base ; PA = addition ; PM = multiplication ; PE = exponentiation }
