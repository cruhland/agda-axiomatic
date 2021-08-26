open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.OrderingDecl PA using (Ordering)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Integers : Set₁ where
  field
    ZB : Base
    ZA : Addition ZB
    ZN : Negation ZB ZA
    ZM : Multiplication ZB ZA ZN
    ZS : Sign ZB ZA ZN ZM
    ZO : Ordering ZB ZA ZN ZM ZS

  open Addition ZA public
  open Base ZB public
  open LiteralImpl ZB public
  open Multiplication ZM public
  open Negation ZN public
  open Ordering ZO public
  open Sign ZS public

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Integers.MultiplicationPartialImpl
  import net.cruhland.axioms.Integers.NegationPartialImpl
  import net.cruhland.axioms.Integers.NegationPartialImplSub
  import net.cruhland.axioms.Integers.OrderingDefaultImpl
  import net.cruhland.axioms.Integers.SignPartialImpl
  import net.cruhland.axioms.Integers.SignPartialImplNat
