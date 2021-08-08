import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Ordering using (_<_; _≮_; LessThan)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl as LtBaseDecl
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  as LteBaseDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊥)

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
    {{<-substitutive-≃}} : AA.Substitutive² _<_ _≃_ _⟨→⟩_
    {{<-substitutive-+}} : AA.Substitutive² _+_ _<_ _<_
    <-compatible-+ : {n₁ n₂ m₁ m₂ : ℕ} → n₁ < n₂ → m₁ < m₂ → n₁ + m₁ < n₂ + m₂
    n<sn : {n : ℕ} → n < step n
    n≮0 : {n : ℕ} → n ≮ 0
    <-from-pos : {n : ℕ} → S.Positive n → 0 < n
    <-asymmetric : {n m : ℕ} → n < m → m < n → ⊥
