open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
open import net.cruhland.axioms.Rationals.DivisionDecl PA Z using (Division)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)
open import net.cruhland.axioms.Rationals.SignDecl PA Z using (Sign)

record Rationals : Set₁ where
  field
    QB : Base
    QA : Addition QB
    QS : Sign QB
    QN : Negation QB QA
    QD : Division QB QA QN
    QM : Multiplication QB QA QN
    QR : Reciprocal QB QA QN QM

  open Addition QA public
  open Base QB public
  open Division QD public
  open LiteralImpl QB public
  open Multiplication QM public
  open Negation QN public
  open Reciprocal QR public
  open Sign QS public

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Rationals.NegationPartialImpl
  import net.cruhland.axioms.Rationals.DivisionPartialImplBase
  import net.cruhland.axioms.Rationals.DivisionPartialImplProperties
  import net.cruhland.axioms.Rationals.SignDefaultImpl
