import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; ¬-intro; _↯_)

module net.cruhland.models.Integers.NatPair.SignImplNat
  (PA : PeanoArithmetic) where

import net.cruhland.axioms.Integers.SignDecl PA as SignDecl
import net.cruhland.axioms.Integers.SignPartialImplNat PA as SignPartialImplNat
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (ZM)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)

private
  module ℕ = PeanoArithmetic PA
  module ℤ where
    open import net.cruhland.models.Integers.NatPair.AdditionImpl PA public
    open import net.cruhland.axioms.Integers.LiteralImpl PA ZB public
    open import net.cruhland.models.Integers.NatPair.BaseImpl PA public
    open import net.cruhland.models.Integers.NatPair.MultiplicationImpl PA
      public
    open import net.cruhland.models.Integers.NatPair.NegationImpl PA public

open ℤ using (_—_; ℤ)
open SignDecl.SignPredefs ZB ZA ZN ZM public
open SignPartialImplNat.SignPredefs ZB ZA ZN ZM public

instance
  sign-trichotomy : S.Trichotomy ℤ
  sign-trichotomy = S.trichotomy-intro sign-tri
    where
      sign-tri :
        (a : ℤ) → AA.ExactlyOneOfThree (a ≃ 0) (S.Positive a) (S.Negative a)
      sign-tri x@(x⁺ — x⁻) = AA.exactlyOneOfThree 1of3 ¬2of3
        where
          x⁺<≃>x⁻ = ℕ.order-trichotomy x⁺ x⁻

          1of3 : AA.OneOfThree (x ≃ 0) (S.Positive x) (S.Negative x)
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
             in AA.3rd (≃posℕ-intro pos[d] (ℤ.≃₀-intro x⁺+d≃0+x⁻))
          1of3 | AA.2nd x⁺≃x⁻ = AA.1st (ℤ.zero-from-balanced x⁺≃x⁻)
          1of3 | AA.3rd x⁺>x⁻ =
            let x⁻<x⁺ = Ord.>-flip x⁺>x⁻
                d = ℕ.<-diff x⁻<x⁺
                pos[d] = ℕ.<-diff-pos x⁻<x⁺
                x⁻+d≃x⁺ = ℕ.<-elim-diff x⁻<x⁺
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
             in AA.2nd (≃posℕ-intro pos[d] (ℤ.≃₀-intro x⁺+0≃d+x⁻))

          ¬2of3 : ¬ AA.TwoOfThree (x ≃ 0) (S.Positive x) (S.Negative x)
          ¬2of3 = ¬-intro λ
            { (AA.1∧2 x≃0 pos[x]) → x≃0 ↯ (S.pos≄0 pos[x])
            ; (AA.1∧3 x≃0 neg[x]) → x≃0 ↯ (S.neg≄0 neg[x])
            ; (AA.2∧3
                  (≃posℕ-intro {m} pos[m] (ℤ.≃₀-intro x⁺+0≃m+x⁻))
                  (≃posℕ-intro {n} pos[n] (ℤ.≃₀-intro x⁺+n≃0+x⁻))) →
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
                    x⁺>x⁻ = Ord.<-flip x⁻<x⁺
                    x⁺<>x⁻ = AA.1∧3 x⁺<x⁻ x⁺>x⁻
                    ¬x⁺<>x⁻ = AA.ExactlyOneOfThree.at-most-one x⁺<≃>x⁻
                 in x⁺<>x⁻ ↯ ¬x⁺<>x⁻
            }

-- Include everything from the partial impl
private
  open import net.cruhland.axioms.Integers.SignPartialImplNat PA
    using (SignPropertiesNat)

  signPropertiesNat : SignPropertiesNat ZB ZA ZN ZM
  signPropertiesNat = record {}

open SignPropertiesNat signPropertiesNat public
  hiding (sign-trichotomy)

instance
  positivity-common : S.PositivityCommon ℤ
  positivity-common = record {}

  negativity-common : S.NegativityCommon ℤ
  negativity-common = record {}

  sign-common : S.SignCommon ℤ
  sign-common =
    record { neg-Positive = neg-Positive ; neg-Negative = neg-Negative }
