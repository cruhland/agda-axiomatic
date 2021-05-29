import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Multiplication.BaseDecl
  using (MultiplicationBase)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Multiplication.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (Z- : Negation PA ZB ZP Z+)
  (MB : MultiplicationBase PA ZB ZP Z+ Z-)
  where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)
private module ℤ- = Negation Z-
private module ℤP = Properties ZP

neg-mult : {a : ℤ} → -1 * a ≃ - a
neg-mult {a} =
  begin
    -1 * a
  ≃⟨ AA.subst₂ (ℤ-.neg-literal≃nat-literal 1) ⟩
    (- 1) * a
  ≃˘⟨ AA.fnOpComm ⟩
    - (1 * a)
  ≃⟨ AA.subst₁ AA.ident ⟩
    - a
  ∎

instance
  private
    *-distributive-subᴸ : AA.Distributive AA.handᴸ _*_ _-_
    *-distributive-subᴸ = AA.distributive *-distrib-subᴸ
      where
        *-distrib-subᴸ : {a b c : ℤ} → c * (a - b) ≃ c * a - c * b
        *-distrib-subᴸ {a} {b} {c} =
          begin
            c * (a - b)
          ≃⟨ AA.subst₂ ℤ-.sub-defn ⟩
            c * (a + (- b))
          ≃⟨ AA.distrib ⟩
            c * a + c * (- b)
          ≃˘⟨ AA.subst₂ AA.fnOpComm ⟩
            c * a + (- (c * b))
          ≃˘⟨ ℤ-.sub-defn ⟩
            c * a - c * b
          ∎

    *-distributive-subᴿ : AA.Distributive AA.handᴿ _*_ _-_
    *-distributive-subᴿ = AA.distributiveᴿ-from-distributiveᴸ

  *-distributive-sub : AA.Distributive² _*_ _-_
  *-distributive-sub = AA.distributive²
