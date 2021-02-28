module net.cruhland.models.Peano.LteLeft where

open import Data.Nat using (suc; s≤s; zero; z≤n) renaming (_≤_ to _≤ᴸ_)
open import Data.Nat.Properties using (suc-injective; ≤-refl; ≤-step)
open import Relation.Binary.PropositionalEquality using (cong; refl)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Base as LteBase
open import net.cruhland.models.Function using (_⟨→⟩_; id)
import net.cruhland.models.Peano.Unary as U

open module LB = LteBase U.base U.sign U.addition using
  (_+d≃_; +d≃-intro; 0+d≃n; LteBase)
open PeanoBase U.base using (ℕ; step)

diff : ∀ {n m} → n ≤ᴸ m → ℕ
diff (z≤n {d}) = d
diff (s≤s n≤ᴸm) = diff n≤ᴸm

n≤ᴸm-from-n+d≃m : ∀ {n m d} → n + d ≃ m → n ≤ᴸ m
n≤ᴸm-from-n+d≃m {zero} n+d≃m =
  z≤n
n≤ᴸm-from-n+d≃m {suc n} {suc m} sn+d≡sm =
  s≤s (n≤ᴸm-from-n+d≃m (suc-injective sn+d≡sm))

n+d≃m-from-n≤ᴸm : ∀ {n m} (n≤ᴸm : n ≤ᴸ m) → n + diff n≤ᴸm ≃ m
n+d≃m-from-n≤ᴸm z≤n = refl
n+d≃m-from-n≤ᴸm (s≤s n≤ᴸm) = cong suc (n+d≃m-from-n≤ᴸm n≤ᴸm)

instance
  lessThanOrEqual-≤ᴸ : LessThanOrEqual ℕ
  lessThanOrEqual-≤ᴸ = record { _≤_ = _≤ᴸ_ }

  substitutive-≤ᴸ-≃ᴸ : AA.Substitutive₂ AA.handᴸ _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ᴸ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴸ-≃ᴿ : AA.Substitutive₂ AA.handᴿ _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ᴿ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴸ-≃ : AA.Substitutive₂² _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ = AA.substitutive₂²

  reflexive-≤ᴸ : Eq.Reflexive _≤ᴸ_
  reflexive-≤ᴸ = Eq.reflexive ≤-refl

  substitutive-step-≤ᴸ : AA.Substitutive₁ step _≤ᴸ_ _≤ᴸ_
  substitutive-step-≤ᴸ = AA.substitutive₁ s≤s

≤-base-≤ᴸ : LteBase
≤-base-≤ᴸ = record
  { diff = diff
  ; ≤-intro-diff = n≤ᴸm-from-n+d≃m
  ; ≤-elim-diff = n+d≃m-from-n≤ᴸm
  ; 0≤n = z≤n
  ; ≤-step = ≤-step
  }
