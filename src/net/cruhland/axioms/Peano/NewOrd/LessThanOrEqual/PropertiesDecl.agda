import net.cruhland.axioms.Eq as Eq
open import net.cruhland.axioms.NewOrd using (_≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ; step)

record LteProperties : Set where
  field
    {{≤-transitive}} : Eq.Transitive _≤_

    n≤sn : {n : ℕ} → n ≤ step n
