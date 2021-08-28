import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Ordering as Ord using (_<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_⟨→⟩_)

module net.cruhland.axioms.Rationals.OrderingDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

private
  module RationalPredefs (QB : Base) (QA : Addition QB) where
    open Addition QA public
    open Base QB public

record Ordering (QB : Base) (QA : Addition QB) : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{totalOrder}} : Ord.TotalOrder ℚ
    {{<-substitutive-≃}} : AA.Substitutive² {A = ℚ} _<_ _≃_ _⟨→⟩_
    {{<-substitutive-+}} : AA.Substitutive² {A = ℚ} _+_ _<_ _<_
