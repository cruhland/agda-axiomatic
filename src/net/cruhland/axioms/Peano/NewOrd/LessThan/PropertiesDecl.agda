import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (_<_; _≮_; LessThan)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTB : LtBase PB PS PA LTEB) where

open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL

record LtProperties : Set where
  field
    {{<-transitive}} : Eq.Transitive _<_
    {{<-substitutive-≃}} : AA.Substitutive₂² _<_ _≃_ _⟨→⟩_
    n<sn : {n : ℕ} → n < step n
    n≮0 : {n : ℕ} → n ≮ 0
