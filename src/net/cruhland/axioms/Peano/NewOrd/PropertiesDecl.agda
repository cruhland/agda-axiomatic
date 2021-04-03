import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Logic using (_∨_)

module net.cruhland.axioms.Peano.NewOrd.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTB : LtBase PB PS PA LTEB) where

open PeanoBase PB using (ℕ; step)

record OrderingProperties : Set where
  field
    ≤-dec-≃ : {n m : ℕ} → n ≤ m → n ≃ m ∨ n ≄ m
    ≤-split : {n m : ℕ} → n ≤ m → n < m ∨ n ≃ m
    s≤-from-< : {n m : ℕ} → n < m → step n ≤ m
    <-from-s≤ : {n m : ℕ} → step n ≤ m → n < m
    order-trichotomy : {n m : ℕ} → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
