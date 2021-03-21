import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
open import net.cruhland.axioms.NewOrd using (_≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesImplBase
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

private module ℕ+ = Addition PA
open PeanoBase PB using (ℕ; step)
private module ℕ≤ = LteBase LTEB

instance
  ≤-transitive : Eq.Transitive _≤_
  ≤-transitive = Eq.transitive ≤-trans
    where
      ≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
      ≤-trans n≤m m≤p =
        let n+a≃m = ℕ≤.≤-elim-diff n≤m
            m+b≃p = ℕ≤.≤-elim-diff m≤p
         in ℕ≤.≤-intro-diff (AA.a[bc]-chain n+a≃m m+b≃p)

n≤sn : {n : ℕ} → n ≤ step n
n≤sn = ℕ≤.≤-step Eq.refl
