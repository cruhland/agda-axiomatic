import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (_≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_⟨→⟩_)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ; step)

record LteProperties : Set where
  field
    {{≤-transitive}} : Eq.Transitive _≤_
    {{≤-antisymmetric}} : AA.Antisymmetric _≤_
    {{≤-substitutive-≃}} : AA.Substitutive₂² _≤_ _≃_ _⟨→⟩_

    n≤sn : {n : ℕ} → n ≤ step n
