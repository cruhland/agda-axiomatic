import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Ordering as Ord using (_≤_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.OrderingDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Ordering (ZB : Base) : Set₁ where
  open Base ZB using (ℤ)

  field
    {{lessThanOrEqual}} : Ord.LessThanOrEqual ℤ
    {{≤-antisymmetric}} : AA.Antisymmetric {A = ℤ} _≤_

    {{lessThan}} : Ord.LessThan ℤ
