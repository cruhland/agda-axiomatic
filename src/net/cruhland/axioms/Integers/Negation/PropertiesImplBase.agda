import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl using (NegationBase)
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.axioms.Integers.Negation.PropertiesImplBase
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (NB : NegationBase PA ZB Z+)
  where

private module ℕ = PeanoArithmetic PA
open Base ZB using (ℤ)

instance
  neg-literal : FromNeg.Negative ℤ
  neg-literal = record { Constraint = const ⊤ ; fromNeg = λ n → - (n as ℤ) }

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive {a} =
  begin
    - (- a)
  ≃˘⟨ AA.ident ⟩
    - (- a) + 0
  ≃˘⟨ AA.subst₂ AA.inv ⟩
    - (- a) + ((- a) + a)
  ≃˘⟨ AA.assoc ⟩
    (- (- a) + (- a)) + a
  ≃⟨ AA.subst₂ AA.inv ⟩
    0 + a
  ≃⟨ AA.ident ⟩
    a
  ∎
