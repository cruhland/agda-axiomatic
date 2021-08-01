import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.NegationDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl

private module IntegerPredefs (ZB : Base) (ZA : Addition ZB) where
  open Addition ZA public
  open Base ZB public
  open LiteralImpl ZB public

record Negation (ZB : Base) (ZA : Addition ZB) : Set₁ where
  private open module ℤ = IntegerPredefs ZB ZA using (ℤ)

  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
    {{neg-injective}} : AA.Injective -_ _≃_ _≃_
    {{neg-inverse}} : AA.Inverse² {A = ℤ} -_ (const ⊤) _+_ 0

    neg-involutive : {a : ℤ} → - (- a) ≃ a
    neg-zero : - 0 ≃ 0

    {{sub-dash}} : Op.Dash₂ ℤ
    sub-defn : {a b : ℤ} → a - b ≃ a + (- b)
    {{sub-substitutive}} : AA.Substitutive² _-_ _≃_ _≃_
    sub-same≃zero : {a : ℤ} → a - a ≃ 0
    ≃-from-zero-sub : {a b : ℤ} → a - b ≃ 0 → a ≃ b
    ≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
    ≃ᴿ-+ᴸ-toᴿ : {a b c : ℤ} → a ≃ b + c → a - b ≃ c
