import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.OrderingDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Ordering (ZB : Base) : Set₁ where
  open Base ZB using (ℤ)

  field
    {{lessThanOrEqual}} : Ord.LessThanOrEqual ℤ
    {{lessThan}} : Ord.LessThan ℤ
