open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Operators using (_+_)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.OrderingPartialImpl
  (PA : PeanoArithmetic) (ZB : Base PA) (Z+ : Addition PA ZB) where

open PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)

record _≤₀_ (a b : ℤ) : Set where
  constructor ≤₀-intro
  field
    {d} : ℕ
    a+d≃b : a + (d as ℤ) ≃ b

record _<₀_ (a b : ℤ) : Set where
  constructor <₀-intro
  field
    a≤b : a ≤₀ b
    a≄b : a ≄ b

instance
  lessThanOrEqual : Ord.LessThanOrEqual ℤ
  lessThanOrEqual = Ord.lessThanOrEqual _≤₀_

  lessThan : Ord.LessThan ℤ
  lessThan = Ord.lessThan _<₀_
