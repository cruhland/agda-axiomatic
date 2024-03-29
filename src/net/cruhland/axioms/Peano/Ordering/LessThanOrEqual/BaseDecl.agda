import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (_+_; _≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL

record LteBase : Set₁ where
  field
    {{ltEq}} : Op.LtEq ℕ
    {{gtEq}} : Op.GtEq ℕ

    ≤-zeroᴸ : {n : ℕ} → 0 ≤ n

    {{≤-substitutive-step}} : AA.Substitutive₁ step _≤_ _≤_
    ≤-widenᴿ : {n m : ℕ} → n ≤ m → n ≤ step m

    ≤-diff : {n m : ℕ} → n ≤ m → ℕ
    ≤-intro-diff : {n m d : ℕ} → n + d ≃ m → n ≤ m
    ≤-elim-diff : {n m : ℕ} (n≤m : n ≤ m) → n + ≤-diff n≤m ≃ m
