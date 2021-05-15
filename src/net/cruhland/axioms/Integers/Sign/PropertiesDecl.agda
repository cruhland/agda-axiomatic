open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Sign.PropertiesDecl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)
open import net.cruhland.axioms.Integers.Sign.BaseDecl PA ZB Z+ Z-
  using (SignBase)

record SignProperties (SB : SignBase) : Set where
  field
    1-Positive : Positive {A = ℤ} 1
