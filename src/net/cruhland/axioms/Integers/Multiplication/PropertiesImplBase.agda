import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Multiplication.BaseDecl
  using (MultiplicationBase)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.SignDecl using (Sign)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; Positive)
import net.cruhland.models.Function
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Multiplication.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  (ZS : Sign PA ZB Z+ Z-)
  (MB : MultiplicationBase PA ZB Z+ Z-)
  where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)
private module ℤ- = Negation Z-
private module ℤS = Sign ZS

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

  private
    *-absorptiveᴸ : AA.Absorptive AA.handᴸ _*_ 0
    *-absorptiveᴸ = AA.absorptive *-absorbᴸ
      where
        *-absorbᴸ : {a : ℤ} → 0 * a ≃ 0
        *-absorbᴸ {a} =
          begin
            0 * a
          ≃˘⟨ AA.subst₂ ℤ-.sub-same≃zero ⟩
            (1 - 1) * a
          ≃⟨ AA.distrib ⟩
            1 * a - 1 * a
          ≃⟨ ℤ-.sub-same≃zero ⟩
            0
          ∎

    *-absorptiveᴿ : AA.Absorptive AA.handᴿ _*_ 0
    *-absorptiveᴿ = AA.absorptiveᴿ-from-absorptiveᴸ {A = ℤ}

  *-absorptive : AA.Absorptive² _*_ 0
  *-absorptive = AA.absorptive² {A = ℤ}

  neg-compatible-+ : AA.IsCompatible₂ -_ _+_ _+_ _≃_
  neg-compatible-+ = AA.isCompatible₂ neg-compat-+
    where
      neg-compat-+ : {a b : ℤ} → - (a + b) ≃ (- a) + (- b)
      neg-compat-+ {a} {b} =
        begin
          - (a + b)
        ≃˘⟨ neg-mult ⟩
          -1 * (a + b)
        ≃⟨ AA.distrib ⟩
          -1 * a + -1 * b
        ≃⟨ AA.subst₂ neg-mult ⟩
          (- a) + -1 * b
        ≃⟨ AA.subst₂ neg-mult ⟩
          (- a) + (- b)
        ∎

neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  begin
    - (a - b)
  ≃⟨ AA.subst₁ ℤ-.sub-defn ⟩
    - (a + (- b))
  ≃⟨ AA.isCompat₂ ⟩
    (- a) + (- (- b))
  ≃⟨ AA.subst₂ ℤ-.neg-involutive ⟩
    (- a) + b
  ≃⟨ AA.comm ⟩
    b + (- a)
  ≃˘⟨ ℤ-.sub-defn ⟩
    b - a
  ∎

sub-sign-swap : {a b : ℤ} → Negative (a - b) → Positive (b - a)
sub-sign-swap neg[a-b] =
  let pos[-[a-b]] = ℤS.neg-Negative neg[a-b]
   in AA.subst₁ neg-sub-swap pos[-[a-b]]
