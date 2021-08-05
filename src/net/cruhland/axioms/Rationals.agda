open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)

record Rationals : Set₁ where
  field
    QB : Base
    QA : Addition QB
    QN : Negation QB QA
    QM : Multiplication QB QA
    QR : Reciprocal QB QA QM

  open Addition QA public
  open Base QB public
  open LiteralImpl QB public
  open Multiplication QM public
  open Negation QN public
  open Reciprocal QR public

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Rationals.NegationPartialImpl
  import net.cruhland.axioms.Rationals.ReciprocalPartialImpl
