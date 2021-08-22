import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignPartialImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZA : Addition PA ZB)
  (ZN : Negation PA ZB ZA)
  where

import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
import net.cruhland.axioms.Integers.SignDecl PA as SignDecl

private
  module ℕ = PeanoArithmetic PA
  module ℤ where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Negation ZN public
    open SignDecl.SignPredefs ZB ZA ZN public

open ℕ using (ℕ)
open ℤ using (ℤ; _≃±1)

record SignProperties : Set₁ where
  field
    {{positivity}} : S.Positivity ℤ
    from-ℕ-preserves-pos : {n : ℕ} → S.Positive n → S.Positive (n as ℤ)

  instance
    ≃±1-substitutive : AA.Substitutive₁ _≃±1 _≃_ _⟨→⟩_
    ≃±1-substitutive = AA.substitutive₁ ≃±1-subst
      where
        ≃±1-subst : {s₁ s₂ : ℤ} → s₁ ≃ s₂ → s₁ ≃±1 → s₂ ≃±1
        ≃±1-subst s₁≃s₂ (ℤ.≃+1-intro s₁≃1) =
          let s₂≃1 = Eq.trans (Eq.sym s₁≃s₂) s₁≃1
           in ℤ.≃+1-intro s₂≃1
        ≃±1-subst s₁≃s₂ (ℤ.≃-1-intro s₁≃-1) =
          let s₂≃-1 = Eq.trans (Eq.sym s₁≃s₂) s₁≃-1
           in ℤ.≃-1-intro s₂≃-1

  ≃±1-absorbs-neg : {a : ℤ} → - a ≃±1 → a ≃±1
  ≃±1-absorbs-neg {a} (ℤ.≃+1-intro -a≃1) =
    let a≃-1 =
          begin
            a
          ≃˘⟨ AA.inv-involutive ⟩
            - (- a)
          ≃⟨ AA.subst₁ -a≃1 ⟩
            - 1
          ≃⟨⟩
            -1
          ∎
     in ℤ.≃-1-intro a≃-1
  ≃±1-absorbs-neg {a} (ℤ.≃-1-intro -a≃-1) =
    let a≃1 = AA.inject -a≃-1
     in ℤ.≃+1-intro a≃1

  1-Positive : S.Positive {A = ℤ} 1
  1-Positive = from-ℕ-preserves-pos (ℕ.Pos-intro-≄0 ℕ.step≄zero)
