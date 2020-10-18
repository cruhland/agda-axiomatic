module net.cruhland.models.Peano.Unary where

open import Data.Nat using (ℕ; _+_; _*_; _^_; zero) renaming (suc to step)
open import Data.Nat.Properties
  using (+-comm; *-comm) renaming (suc-injective to step-injective)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; ≢-sym; trans)
open import net.cruhland.axioms.Eq using (Eq)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)

ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (step k)) → ∀ n → P n
ind P Pz Ps zero = Pz
ind P Pz Ps (step n) = ind (P ∘ step) (Ps Pz) Ps n

data _≢ⁱ_ : ℕ → ℕ → Set where
  instance
    z≢s : ∀ {m} → zero ≢ⁱ step m
    s≢z : ∀ {n} → step n ≢ⁱ zero
    s≢s : ∀ {n m} {{_ : n ≢ⁱ m}} → step n ≢ⁱ step m

≢ⁱ-elim : ∀ {n m} {{_ : n ≢ⁱ m}} → n ≢ m
≢ⁱ-elim {{z≢s}} = λ ()
≢ⁱ-elim {{s≢z}} = λ ()
≢ⁱ-elim {{s≢s}} = ≢ⁱ-elim ∘ step-injective

instance
  eq : Eq ℕ
  eq = record
    { _≃_ = _≡_
    ; refl = refl
    ; sym = sym
    ; trans = trans
    ; _≄ⁱ_ = _≢ⁱ_
    ; ≄ⁱ-elim = ≢ⁱ-elim
    }

base : Peano
base = record
  { ℕ = ℕ
  ; zero = zero
  ; step = step
  ; eq = eq
  ; step≄zero = λ ()
  ; step-subst = cong step
  ; step-inj = step-injective
  ; ind = ind
  }

addition : Addition base
addition = record
  { _+_ = _+_
  ; +-zeroᴸ = refl
  ; +-stepᴸ = refl
  ; +-substᴸ = λ {_ _ m} → cong (_+ m)
  }

multiplication : Multiplication base addition
multiplication = record
  { _*_ = _*_
  ; *-zeroᴸ = refl
  ; *-stepᴸ = λ {n m} → +-comm m (n * m)
  ; *-substᴸ = λ {_ _ m} → cong (_* m)
  }

exponentiation : Exponentiation base addition multiplication
exponentiation =
  record { _^_ = _^_ ; ^-zeroᴿ = refl ; ^-stepᴿ = λ {n m} → *-comm n (n ^ m) }

peanoArithmetic : PeanoArithmetic
peanoArithmetic = record
  { PB = base ; PA = addition ; PM = multiplication ; PE = exponentiation }
