open import Data.Nat using (ℕ; _+_; zero) renaming (suc to step)
open import Data.Nat.Properties using () renaming (suc-injective to step-inj)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
import net.cruhland.axioms.Peano.Inspect as Inspect
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_; id)

module net.cruhland.models.Peano.Unary.Base where

instance
  ≡-reflexive : Eq.Reflexive _≡_
  ≡-reflexive = Eq.reflexive {A = ℕ} PropEq.refl

  ≡-symmetric : Eq.Symmetric _≡_
  ≡-symmetric = Eq.symmetric {A = ℕ} PropEq.sym

  ≡-transitive : Eq.Transitive _≡_
  ≡-transitive = Eq.transitive {A = ℕ} PropEq.trans

  eq : Eq.Eq ℕ
  eq = Eq.equivalence _≡_

  step-substitutive : AA.Substitutive₁ step _≡_ _≡_
  step-substitutive = AA.substitutive₁ (PropEq.cong step)

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
  ; step≄zero = Eq.≄-intro λ ()
  ; ind = ind
  }

module inspect = Inspect base

instance
  default-positivity = inspect.non-zero-positivity

sign : Sign base
sign = record { Pos-intro-≄0 = id }

instance
  plus : Op.Plus ℕ
  plus = Op.plus _+_

  +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≡_ _≡_
  +-substitutiveᴸ = AA.substitutive₂ λ {_ _ b} → PropEq.cong (_+ b)

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity Eq.refl

  +-fnOpCommutative-stepᴸ : AA.FnOpCommutative AA.handᴸ step _+_
  +-fnOpCommutative-stepᴸ = AA.fnOpCommutative Eq.refl

addition : Addition base sign
addition = record {}
