module net.cruhland.models.Peano.Unary.LteBaseImplLeft where

open import Data.Nat
  using (ℕ; s≤s; z≤n; zero) renaming (_≤_ to _≤ᴸ_; suc to step)
open import Data.Nat.Properties
  using (≤-refl; ≤-step) renaming (suc-injective to step-injective)
open import Relation.Binary.PropositionalEquality using (cong; refl)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Ordering using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
import net.cruhland.models.Peano.Unary.Base

instance
  lessThanOrEqual : LessThanOrEqual ℕ
  lessThanOrEqual = record { _≤_ = _≤ᴸ_ }

  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive ≤-refl

  ≤-substitutive-step : AA.Substitutive₁ step _≤_ _≤_
  ≤-substitutive-step = AA.substitutive₁ s≤s

diff : {n m : ℕ} → n ≤ m → ℕ
diff (z≤n {d}) = d
diff (s≤s n≤m) = diff n≤m

≤-intro-diff : {n m d : ℕ} → n + d ≃ m → n ≤ m
≤-intro-diff {zero} n+d≃m =
  z≤n
≤-intro-diff {step n} {step m} sn+d≃sm =
  s≤s (≤-intro-diff (step-injective sn+d≃sm))

≤-elim-diff : {n m : ℕ} (n≤m : n ≤ m) → n + diff n≤m ≃ m
≤-elim-diff z≤n = refl
≤-elim-diff (s≤s n≤m) = cong step (≤-elim-diff n≤m)

≤-zeroᴸ : {n : ℕ} → 0 ≤ n
≤-zeroᴸ = z≤n

≤-widenᴿ : {n m : ℕ} → n ≤ m → n ≤ step m
≤-widenᴿ = ≤-step
