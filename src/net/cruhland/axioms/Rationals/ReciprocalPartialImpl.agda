open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.ReciprocalPartialImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)

private
  module RationalPredefs
      (QB : Base) (QA : Addition QB) (QM : Multiplication QB QA) where
    open Addition QA public
    open Base QB public
    open LiteralImpl QB public
    open Multiplication QM public

record ReciprocalProperties
    (QB : Base) (QA : Addition QB) (QM : Multiplication QB QA) : Set where
  private open module ℚ = RationalPredefs QB QA QM using (ℚ)

  field
    {{reciprocal}} : Op.SupNegOne ℚ (_≄ 0)

  instance
    slash : Op.Slash ℚ (_≄ 0)
    slash = Op.division
