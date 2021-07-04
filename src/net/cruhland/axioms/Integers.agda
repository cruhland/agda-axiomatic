open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.OrderingDecl PA using (Ordering)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Integers : Set₁ where
  field
    ZB : Base
    Z+ : Addition ZB
    Z- : Negation ZB Z+
    ZS : Sign ZB Z+ Z-
    Z* : Multiplication ZB Z+ Z- ZS
    Z< : Ordering ZB Z+ Z- ZS

  open Addition Z+ public
  open Base ZB public
  open Multiplication Z* public
  open Negation Z- public
  open Ordering Z< public
  open Sign ZS public

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Integers.BasePartialImpl
  import net.cruhland.axioms.Integers.MultiplicationPartialImpl
  import net.cruhland.axioms.Integers.NegationPartialImpl
  import net.cruhland.axioms.Integers.NegationPartialImplSub
  import net.cruhland.axioms.Integers.OrderingDefaultImpl
  import net.cruhland.axioms.Integers.SignPartialImpl
  import net.cruhland.axioms.Integers.SignPartialImplNat
