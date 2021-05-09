import Agda.Builtin.FromNeg as FromNeg
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.Negation.PropertiesDecl
  (PA : PeanoArithmetic) (ZB : Base PA) (Z+ : Addition PA ZB) where

open Base ZB using (ℤ)
open import net.cruhland.axioms.Integers.Negation.BaseDecl PA ZB Z+
  using (NegationBase)

record NegationProperties (NB : NegationBase) : Set₁ where
  field
    {{neg-literal}} : FromNeg.Negative ℤ
    neg-involutive : {a : ℤ} → - (- a) ≃ a
