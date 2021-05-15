import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Negation.PropertiesDecl
  (PA : PeanoArithmetic) (ZB : Base PA) (Z+ : Addition PA ZB) where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)
open import net.cruhland.axioms.Integers.Negation.BaseDecl PA ZB Z+
  using (NegationBase)

record NegationProperties (NB : NegationBase) : Set₁ where
  field
    {{neg-literal}} : FromNeg.Negative ℤ
    neg-involutive : {a : ℤ} → - (- a) ≃ a
    neg-zero : - 0 ≃ 0

    {{sub-dash}} : Op.Dash₂ ℤ
    {{sub-substitutive}} : AA.Substitutive₂² _-_ _≃_ _≃_
    ≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
