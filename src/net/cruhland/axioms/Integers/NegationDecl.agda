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

record Negation (ZB : Base) (Z+ : Addition ZB) : Set₁ where
  open Base ZB using (ℤ)

  field
    {{neg-dash}} : Op.Dashᴸ ℤ
    {{neg-substitutive}} : AA.Substitutive₁ -_ _≃_ _≃_
    {{neg-inverse}} : AA.Inverse² {A = ℤ} -_ (const ⊤) _+_ 0

    {{neg-literal}} : FromNegLiteral ℤ
    neg-literal≃nat-literal :
      (n : Nat) → fromNegLiteral n ≃ - (fromNatLiteral n)

    neg-involutive : {a : ℤ} → - (- a) ≃ a
    neg-zero : - 0 ≃ 0

    {{sub-dash}} : Op.Dash₂ ℤ
    sub-defn : {a b : ℤ} → a - b ≃ a + (- b)
    {{sub-substitutive}} : AA.Substitutive² _-_ _≃_ _≃_
    sub-same≃zero : {a : ℤ} → a - a ≃ 0
    ≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Integers.NegationPartialImpl
