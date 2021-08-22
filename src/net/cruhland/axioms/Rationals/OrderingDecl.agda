open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.OrderingDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

private
  module RationalPredefs (QB : Base) where
    open Base QB public

record Ordering (QB : Base) : Set₁ where
  private open module ℚ = RationalPredefs QB using (ℚ)

  field
    {{totalOrder}} : Ord.TotalOrder ℚ
