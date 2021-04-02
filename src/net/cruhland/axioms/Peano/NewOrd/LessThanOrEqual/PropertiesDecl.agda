import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (_≤_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (Dec)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕ≤ = LteBase LTEB

record LteProperties : Set₁ where
  field
    {{≤-transitive}} : Eq.Transitive _≤_
    {{≤-antisymmetric}} : AA.Antisymmetric _≤_
    {{≤-substitutive-≃}} : AA.Substitutive₂² _≤_ _≃_ _⟨→⟩_
    ≤-intro-≃ : {n m : ℕ} → n ≃ m → n ≤ m
    zero-diff : {n m : ℕ} (n≤m : n ≤ m) → ℕ≤.≤-diff n≤m ≃ 0 → n ≃ m
    _≤?_ : (n m : ℕ) → Dec (n ≤ m)

    {{≤-injective-step}} : AA.Injective step _≤_ _≤_
    n≤sn : {n : ℕ} → n ≤ step n
    ≤-widenᴸ : {n m : ℕ} → step n ≤ m → n ≤ m

    {{≤-substitutive-+}} : AA.Substitutive₂² _+_ _≤_ _≤_
    {{≤-cancellative-+}} : AA.Cancellative² _+_ _≤_
    intro-diff-id :
      {n m d : ℕ} (n+d≃m : n + d ≃ m) → ℕ≤.≤-diff (ℕ≤.≤-intro-diff n+d≃m) ≃ d
