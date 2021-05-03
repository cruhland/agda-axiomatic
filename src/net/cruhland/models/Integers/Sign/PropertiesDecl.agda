import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; Positive)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.Sign.PropertiesDecl
    (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.Base PA using (ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Literals PA as ℤL
import net.cruhland.models.Integers.Negation PA as ℤ-
open import net.cruhland.models.Integers.Sign.BaseDecl PA using (SignBase)

record SignProperties (SB : SignBase) : Set where
  field
    1-Positive : Positive {A = ℤ} 1
    neg-Positive : {a : ℤ} → Positive a → Negative (- a)
    neg-Negative : {a : ℤ} → Negative a → Positive (- a)
    trichotomy :
      (x : ℤ) → AA.ExactlyOneOfThree (Negative x) (x ≃ 0) (Positive x)
