import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Ordering using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl as LtBaseDecl
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  as LteBaseDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Logic using (_∨_; Dec)

module net.cruhland.axioms.Peano.Ordering.PropertiesDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  where

open PeanoBase PB using (ℕ; step)
open LtBaseDecl PB PS PA using (LtBase)
open LteBaseDecl PB PS PA using (LteBase)

record OrderingProperties (LTEB : LteBase) (LTB : LtBase LTEB) : Set₁ where
  field
    ≤-dec-≃ : {n m : ℕ} → n ≤ m → n ≃ m ∨ n ≄ m
    ≤-split : {n m : ℕ} → n ≤ m → n < m ∨ n ≃ m
    s≤-from-< : {n m : ℕ} → n < m → step n ≤ m
    <-from-s≤ : {n m : ℕ} → step n ≤ m → n < m
    order-trichotomy : (n m : ℕ) → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
    ≤s-split : {n m : ℕ} → n ≤ step m → n ≤ m ∨ n ≃ step m
    <s-split : {n m : ℕ} → n < step m → n < m ∨ n ≃ m

    _<?_ : (n m : ℕ) → Dec (n < m)
    strong-ind :
      (P : ℕ → Set) (b : ℕ) →
      (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) → ∀ n → b ≤ n → P n
