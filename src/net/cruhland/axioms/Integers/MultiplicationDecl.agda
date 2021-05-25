import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_; _*_; Star)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)

record Multiplication (ZB : Base) (ZP : Properties ZB) : Set where
  open Base ZB using (ℤ)

  field
    {{star}} : Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
    {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (_as ℤ) _*_
    {{*-identity}} : AA.Identity² _*_ 1
    {{*-distributive}} : AA.Distributive² _*_ _+_
