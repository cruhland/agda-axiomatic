open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Multiplication.BaseDecl
  using (MultiplicationBase)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.SignDecl using (Sign)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.Multiplication.PropertiesDefnBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  (ZS : Sign PA ZB Z+ Z-)
  (MB : MultiplicationBase PA ZB Z+ Z-)
  where

open import net.cruhland.axioms.Integers.Multiplication.PropertiesDecl
  PA ZB Z+ Z- ZS using (MultiplicationProperties)
import net.cruhland.axioms.Integers.Multiplication.PropertiesImplBase
  PA ZB Z+ Z- ZS MB as MP

MP : MultiplicationProperties MB
MP = record { MP }
