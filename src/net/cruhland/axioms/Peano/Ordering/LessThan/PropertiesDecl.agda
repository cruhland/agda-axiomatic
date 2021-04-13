import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Ordering using (_<_; _≮_; LessThan)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl as LtBaseDecl
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  as LteBaseDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  where

open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL
open LtBaseDecl PB PS PA using (LtBase)
open LteBaseDecl PB PS PA using (LteBase)

record LtProperties (LTEB : LteBase) (LTB : LtBase LTEB) : Set where
  field
    {{<-transitive}} : Eq.Transitive _<_
    {{<-substitutive-≃}} : AA.Substitutive₂² _<_ _≃_ _⟨→⟩_
    n<sn : {n : ℕ} → n < step n
    n≮0 : {n : ℕ} → n ≮ 0
