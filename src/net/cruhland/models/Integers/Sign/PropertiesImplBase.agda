import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; neg≄0; Positive; pos≄0)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Integers.Sign.BaseDecl using (SignBase)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; contra)

module net.cruhland.models.Integers.Sign.PropertiesImplBase
    (PA : PeanoArithmetic) (SB : SignBase PA) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Literals PA as ℤL
import net.cruhland.models.Integers.Negation PA as ℤ-
private module ℤS = SignBase SB

1-Positive : Positive {A = ℤ} 1
1-Positive = ℤS.pos-intro-proj ℕ.n<sn

neg-Positive : {a : ℤ} → Positive a → Negative (- a)
neg-Positive = ℤS.neg-intro-proj ∘ ℤS.pos-elim-proj

neg-Negative : {a : ℤ} → Negative a → Positive (- a)
neg-Negative = ℤS.pos-intro-proj ∘ ℤS.neg-elim-proj

trichotomy : (x : ℤ) → AA.ExactlyOneOfThree (Negative x) (x ≃ 0) (Positive x)
trichotomy x@(x⁺ — x⁻) = record { at-least-one = 1of3 ; at-most-one = ¬2of3 }
  where
    x⁺<≃>x⁻ = ℕ.order-trichotomy x⁺ x⁻

    1of3 : AA.OneOfThree (Negative x) (x ≃ 0) (Positive x)
    1of3 with AA.ExactlyOneOfThree.at-least-one x⁺<≃>x⁻
    1of3 | AA.1st x⁺<x⁻ = AA.1st (ℤS.neg-intro-proj x⁺<x⁻)
    1of3 | AA.2nd x⁺≃x⁻ = AA.2nd (ℤ≃.≃-zero x⁺≃x⁻)
    1of3 | AA.3rd x⁺>x⁻ = AA.3rd (ℤS.pos-intro-proj x⁺>x⁻)

    ¬2of3 : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    ¬2of3 (AA.2∧3 x≃0 pos[x]) = contra x≃0 (pos≄0 pos[x])
    ¬2of3 (AA.1∧2 neg[x] x≃0) = contra x≃0 (neg≄0 neg[x])
    ¬2of3 (AA.1∧3 neg[x] pos[x]) =
      let x⁺<>x⁻ = AA.1∧3 (ℤS.neg-elim-proj neg[x]) (ℤS.pos-elim-proj pos[x])
          ¬x⁺<>x⁻ = AA.ExactlyOneOfThree.at-most-one x⁺<≃>x⁻
       in contra x⁺<>x⁻ ¬x⁺<>x⁻
