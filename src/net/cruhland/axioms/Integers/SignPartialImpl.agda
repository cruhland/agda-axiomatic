import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive; Positivity)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignPartialImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤB = Base ZB using (ℤ)
private module ℤ- = Negation Z-
import net.cruhland.axioms.Integers.SignDecl PA as SignDecl
open SignDecl.SignPredefs ZB Z+ Z- using (_≃±1; ≃+1-intro; ≃-1-intro)

record SignProperties : Set₁ where
  field
    {{positivity}} : Positivity {A = ℤ} 0
    from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)

  instance
    ≃±1-substitutive : AA.Substitutive₁ _≃±1 _≃_ _⟨→⟩_
    ≃±1-substitutive = AA.substitutive₁ ≃±1-subst
      where
        ≃±1-subst : {s₁ s₂ : ℤ} → s₁ ≃ s₂ → s₁ ≃±1 → s₂ ≃±1
        ≃±1-subst s₁≃s₂ (≃+1-intro s₁≃1) =
          ≃+1-intro (Eq.trans (Eq.sym s₁≃s₂) s₁≃1)
        ≃±1-subst s₁≃s₂ (≃-1-intro s₁≃-1) =
          ≃-1-intro (Eq.trans (Eq.sym s₁≃s₂) s₁≃-1)

  ≃±1-absorbs-neg : {a : ℤ} → - a ≃±1 → a ≃±1
  ≃±1-absorbs-neg {a} (≃+1-intro -a≃1) =
    let a≃-1 =
          begin
            a
          ≃˘⟨ ℤ-.neg-involutive ⟩
            - (- a)
          ≃⟨ AA.subst₁ -a≃1 ⟩
            - 1
          ≃˘⟨ ℤ-.neg-literal≃nat-literal 1 ⟩
            -1
          ∎
     in ≃-1-intro a≃-1
  ≃±1-absorbs-neg {a} (≃-1-intro -a≃-1) =
    let -1≃-[1] = ℤ-.neg-literal≃nat-literal 1
        a≃1 = AA.inject (Eq.trans -a≃-1 -1≃-[1])
     in ≃+1-intro a≃1

  fromNatLiteral-preserves-pos :
    (n : Nat) → Positive {A = ℕ} (fromNatLiteral n) →
    Positive {A = ℤ} (fromNatLiteral n)
  fromNatLiteral-preserves-pos n pos[n] =
    let pos[a] = from-ℕ-preserves-pos pos[n]
     in AA.subst₁ (Eq.sym (ℤB.fromNatLiteral≃casts n)) pos[a]

  1-Positive : Positive 1
  1-Positive = fromNatLiteral-preserves-pos 1 (ℕ.Pos-intro-≄0 ℕ.step≄zero)
