import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Integers.Sign.BaseDecl using (SignBase)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Sign.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (Z- : Negation PA ZB ZP Z+)
  (SB : SignBase PA ZB ZP Z+ Z-)
  where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)
private module ℤP = Properties ZP
private module ℤSB = SignBase SB

fromNatLiteral-preserves-pos :
  (n : Nat) → Positive {A = ℕ} (fromNatLiteral n) →
  Positive {A = ℤ} (fromNatLiteral n)
fromNatLiteral-preserves-pos n pos[n] =
  let pos[a] = ℤSB.from-ℕ-preserves-pos pos[n]
   in AA.subst₁ (ℤP.casts≃fromNatLiteral n) pos[a]

1-Positive : Positive 1
1-Positive = fromNatLiteral-preserves-pos 1 (ℕ.Pos-intro-≄0 ℕ.step≄zero)
