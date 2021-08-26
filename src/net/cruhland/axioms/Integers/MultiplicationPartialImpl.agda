import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.MultiplicationPartialImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

private
  open module ℕ = PeanoArithmetic PA using (ℕ)
  module IntegerPredefs
      (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Negation ZN public

record MultiplicationProperties
    (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) : Set where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN using (ℤ)

  field
    {{star}} : Op.Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-associative}} : AA.Associative {A = ℤ} _*_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
    {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (AA.tc₁ (_as ℤ)) _*_ _*_ _≃_
    {{*-identity}} : AA.Identity² {A = ℤ} _*_ 1

    {{*-distributive}} : AA.Distributive² {A = ℤ} (AA.tc₂ _*_) _+_
    {{*-comm-with-neg}} : AA.FnOpCommutative² -_ -_ (AA.tc₂ _*_)

  neg-mult : {a : ℤ} → -1 * a ≃ - a
  neg-mult {a} =
    begin
      -1 * a
    ≃⟨⟩
      (- 1) * a
    ≃˘⟨ AA.fnOpCommᴸ ⟩
      - (1 * a)
    ≃⟨ AA.subst₁ AA.ident ⟩
      - a
    ∎

  instance
    *-distributive-subᴸ : AA.Distributive AA.handᴸ (AA.tc₂ _*_) _-_
    *-distributive-subᴸ = AA.distributive *-distrib-subᴸ
      where
        *-distrib-subᴸ : {a b c : ℤ} → c * (a - b) ≃ c * a - c * b
        *-distrib-subᴸ {a} {b} {c} =
          begin
            c * (a - b)
          ≃⟨ AA.subst₂ ℤ.sub-defn ⟩
            c * (a + (- b))
          ≃⟨ AA.distrib ⟩
            c * a + c * (- b)
          ≃˘⟨ AA.subst₂ AA.fnOpCommᴿ ⟩
            c * a + (- (c * b))
          ≃˘⟨ ℤ.sub-defn ⟩
            c * a - c * b
          ∎

    *-distributive-subᴿ : AA.Distributive AA.handᴿ (AA.tc₂ _*_) _-_
    *-distributive-subᴿ = AA.distributiveᴿ-from-distributiveᴸ

    *-distributive-sub : AA.Distributive² (AA.tc₂ _*_) _-_
    *-distributive-sub = AA.distributive²

    private
      *-absorptiveᴸ : AA.Absorptive AA.handᴸ (AA.tc₂ _*_)
      *-absorptiveᴸ = AA.absorptive *-absorbᴸ
        where
          *-absorbᴸ : {a : ℤ} → 0 * a ≃ 0
          *-absorbᴸ {a} =
            begin
              0 * a
            ≃˘⟨ AA.subst₂ ℤ.sub-same≃zero ⟩
              (1 - 1) * a
            ≃⟨ AA.distrib ⟩
              1 * a - 1 * a
            ≃⟨ ℤ.sub-same≃zero ⟩
              0
            ∎

      *-absorptiveᴿ : AA.Absorptive AA.handᴿ (AA.tc₂ _*_)
      *-absorptiveᴿ = AA.absorptiveᴿ-from-absorptiveᴸ {A = ℤ}

    *-absorptive : AA.Absorptive² (AA.tc₂ _*_)
    *-absorptive = AA.absorptive² {A = ℤ}

    neg-compatible-+ : AA.Compatible₂ (AA.tc₁ λ a → - a) _+_ _+_ _≃_
    neg-compatible-+ = AA.compatible₂ neg-compat-+
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
    ≃⟨ AA.subst₁ ℤ.sub-defn ⟩
      - (a + (- b))
    ≃⟨ AA.compat₂ ⟩
      (- a) + (- (- b))
    ≃⟨ AA.subst₂ AA.inv-involutive ⟩
      (- a) + b
    ≃⟨ AA.comm ⟩
      b + (- a)
    ≃˘⟨ ℤ.sub-defn ⟩
      b - a
    ∎
