import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_; Plus)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.AdditionDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.PropertiesDecl PA using (Properties)

record Addition (ZB : Base) (ZP : Properties ZB) : Set where
  open Base ZB using (ℤ)

  field
    {{plus}} : Plus ℤ
    {{+-substitutive}} : AA.Substitutive² {A = ℤ} _+_ _≃_ _≃_
    {{+-commutative}} : AA.Commutative {A = ℤ} _+_
    {{+-associative}} : AA.Associative {A = ℤ} _+_
    {{+-identity}} : AA.Identity² {A = ℤ} _+_ 0
    {{+-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (_as ℤ) _+_
