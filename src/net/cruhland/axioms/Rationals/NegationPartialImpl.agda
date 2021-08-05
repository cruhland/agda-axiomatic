open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.NegationPartialImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

private module RationalPredefs (QB : Base) (QA : Addition QB) where
  open Addition QA public
  open Base QB public

record NegationProperties (QB : Base) (QA : Addition QB) : Set where
  private open module ℚ = RationalPredefs QB QA using (ℚ)

  field
    {{neg-dash}} : Op.Dashᴸ ℚ

  instance
    sub-dash : Op.Dash₂ ℚ
    sub-dash = Op.subtraction
