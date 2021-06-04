import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
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

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤB = Base ZB using (ℤ)
private module ℤSB = SignBase SB

fromNatLiteral-preserves-pos :
  (n : Nat) → Positive {A = ℕ} (fromNatLiteral n) →
  Positive {A = ℤ} (fromNatLiteral n)
fromNatLiteral-preserves-pos n pos[n] =
  let pos[a] = ℤSB.from-ℕ-preserves-pos pos[n]
   in AA.subst₁ (Eq.sym (ℤB.fromNatLiteral≃casts n)) pos[a]

1-Positive : Positive 1
1-Positive = fromNatLiteral-preserves-pos 1 (ℕ.Pos-intro-≄0 ℕ.step≄zero)
