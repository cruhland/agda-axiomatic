import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; neg≄0; Positive; pos≄0)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; contra)

module net.cruhland.models.Integers.NatPair.SignImplNat
  (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)

import net.cruhland.axioms.Integers.SignDecl PA as SignDecl
private module ℤS = SignDecl.SignPredefs ZB Z+ Z-

-- Include everything from the partial impl
open import net.cruhland.axioms.Integers.SignPartialImplNat PA ZB Z+ Z- public

trichotomy : (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)
trichotomy x@(x⁺ — x⁻) = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    x⁺<≃>x⁻ = ℕ.order-trichotomy x⁺ x⁻

    1of3 : AA.OneOfThree (Negative x) (x ≃ 0) (Positive x)
    1of3 with AA.ExactlyOneOfThree.at-least-one x⁺<≃>x⁻
    1of3 | AA.1st x⁺<x⁻ =
      let d = ℕ.<-diff x⁺<x⁻
          pos[d] = ℕ.<-diff-pos x⁺<x⁻
          x⁺+d≃x⁻ = ℕ.<-elim-diff x⁺<x⁻
          x⁺+d≃0+x⁻ =
            begin
              x⁺ + d
            ≃⟨ x⁺+d≃x⁻ ⟩
              x⁻
            ≃˘⟨ AA.ident ⟩
              0 + x⁻
            ∎
       in AA.1st (ℤS.≃posℕ-intro pos[d] (≃₀-intro x⁺+d≃0+x⁻))
    1of3 | AA.2nd x⁺≃x⁻ = AA.2nd (ℤB.zero-from-balanced x⁺≃x⁻)
    1of3 | AA.3rd x⁺>x⁻ =
      let d = ℕ.<-diff x⁺>x⁻
          pos[d] = ℕ.<-diff-pos x⁺>x⁻
          x⁻+d≃x⁺ = ℕ.<-elim-diff x⁺>x⁻
          x⁺+0≃d+x⁻ =
            begin
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ≃˘⟨ x⁻+d≃x⁺ ⟩
              x⁻ + d
            ≃⟨ AA.comm ⟩
              d + x⁻
            ∎
       in AA.3rd (ℤS.≃posℕ-intro pos[d] (≃₀-intro x⁺+0≃d+x⁻))

    ¬2of3 : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    ¬2of3 (AA.2∧3 x≃0 pos[x]) = contra x≃0 (pos≄0 pos[x])
    ¬2of3 (AA.1∧2 neg[x] x≃0) = contra x≃0 (neg≄0 neg[x])
    ¬2of3
      (AA.1∧3
        (ℤS.≃posℕ-intro {n} pos[n] (≃₀-intro x⁺+n≃0+x⁻))
        (ℤS.≃posℕ-intro {m} pos[m] (≃₀-intro x⁺+0≃m+x⁻))) =
      let x⁺+n≃x⁻ =
            begin
              x⁺ + n
            ≃⟨ x⁺+n≃0+x⁻ ⟩
              0 + x⁻
            ≃⟨ AA.ident ⟩
              x⁻
            ∎
          x⁻+m≃x⁺ =
            begin
              x⁻ + m
            ≃⟨ AA.comm ⟩
              m + x⁻
            ≃˘⟨ x⁺+0≃m+x⁻ ⟩
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ∎
          x⁺<x⁻ = ℕ.<-intro-diff pos[n] x⁺+n≃x⁻
          x⁻<x⁺ = ℕ.<-intro-diff pos[m] x⁻+m≃x⁺
          x⁺<>x⁻ = AA.1∧3 x⁺<x⁻ x⁻<x⁺
          ¬x⁺<>x⁻ = AA.ExactlyOneOfThree.at-most-one x⁺<≃>x⁻
       in contra x⁺<>x⁻ ¬x⁺<>x⁻
