open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.Sign.BaseDecl using (SignBase)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Sign.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  (SB : SignBase PA ZB Z+ Z-)
  where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)
private module ℤSB = SignBase SB

1-Positive : Positive {A = ℤ} 1
1-Positive = ℤSB.from-ℕ-preserves-pos (ℕ.Pos-intro-≄0 ℕ.step≄zero)
