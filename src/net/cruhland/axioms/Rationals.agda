open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)

record Rationals : Set₁ where
  field
    QB : Base
    Q+ : Addition QB
    Q* : Multiplication QB

  open Addition Q+ public
  open Base QB public
  open Multiplication Q* public
